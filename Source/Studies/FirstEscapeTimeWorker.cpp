#include "FirstEscapeTimeWorker.h"


void FirstEscapeTimeWorker::setConfig(map<String, String> configs)
{
  for (auto& [key, val] : configs)
  {
    //cout << "key, val : " << key << " " << val << endl;
    juce::var myvar(val);
    if (key == "output")
      outputfilename = val;
    else if (key == "dt_study")
      dt_study = atof(val.toUTF8());
    else if (key == "precision")
      precision = atof(val.toUTF8());
    else if (key == "exitTimePrecision")
      escapeTimePrecision = atof(val.toUTF8());
    else if (key == "startSteadyState")
      startSteadyState = atoi(val.toUTF8());
    else if (key == "debug")
      debug = static_cast<bool>(atoi(val.toUTF8()));
    else if (key == "network")
      network = val;
  }
}



void FirstEscapeTimeWorker::reset()
{
  entities.clear();
  reactions.clear();
  
  // Must be called here, otherwise copy will not work properly
  simul.affectSATIds();
  
  // fill entity array with copies of the ones present in the simulation instance
  // careful, they should not be modified while this study is being called, so I'll probably have to pause the Simulation thread ?
  // or make sure to update the simentity concentration value with the one
  for (auto & ent : simul.entities)
    entities.add(ent->clone().release());
  
  for (auto & ent : entities)
    ent->entity = nullptr; // just make sure this copied SimEntity will not interfere with Entity object
  
  for (auto & r : simul.reactions)
  {
    Array<SimEntity*> reactants;
    Array<SimEntity*> products;
    for (auto & e : r->reactants)
    {
      reactants.add(entities[e->idSAT]);
    }
    for (auto & e : r->products)
    {
      products.add(entities[e->idSAT]);
    }
    SimReaction * copyr = new SimReaction(reactants, products, r->assocRate ,  r->dissocRate,  r->energy);
    reactions.add(copyr);
  }
  
  clearSnapshots(-1);
  
  //escapeTimes.clear();
  //escapeTimes.insertMultiple(0, 0., simul.nRuns);
  escapes.clear();
  Escape defaultEscape = {0., -1, -1};
  escapes.insertMultiple(0, defaultEscape, PhasePlane::getInstance()->nRuns->intValue());
  
  runsTreated.clear();
  /*
  cout << "--- FirstEscapeTime::reset() ---" << endl;
  cout << "--- SimEntity list : " << endl;
  for (auto & ent :entities)
    cout << "\t" << ent->name << endl;
  cout << "--- SimReaction list : " << endl;
  for (auto & r :reactions)
  {
    cout << r->name << endl;
    cout << "reactants : " << endl;
    for (auto& e :r->reactants)
      cout << "\t" << e->name << " : " << e->idSAT << endl;
    cout << "products : " << endl;
    for (auto& e :r->products)
      cout << "\t" << e->name << " : " << e->idSAT << endl;
  }
  */
  
}


void FirstEscapeTimeWorker::submitSnapshot(const ConcentrationGrid& cg, float time, int run)
{
  if (!runsTreated.contains(run)) // do not fill the queue with snapshots if an escape for this run has already been detected
  {
    const juce::ScopedLock sl(dataLock);
    pendingSnapshots.push({cg, time, run});
    
    workAvailable.signal(); // wake up this thread
  }
}

// clean all snapshots for a given run
// if input argument = -1, clean all snapshots
void FirstEscapeTimeWorker::clearSnapshots(const int run)
{
  { // empty the queue with the lock
    const juce::ScopedLock sl(dataLock);
    
    while (!pendingSnapshots.empty())
    {
      if (run == -1 || pendingSnapshots.front().run == run)
        pendingSnapshots.pop();
      else
        break;
    }
    

  } // free the lock
}



void FirstEscapeTimeWorker::run()
{
  while (!threadShouldExit())
  {
    workAvailable.wait(); // thread goes to sleep

    if (threadShouldExit())
      break;
    
    while (!threadShouldExit() && !pendingSnapshots.empty()) // loop to empty all snapshots
    {
      // retrieve the first snapshot in queue
      Snapshot snap;
      {
        const juce::ScopedLock sl(dataLock); // acquire the lock
                
        snap = pendingSnapshots.front(); // get first snapshot waiting
        pendingSnapshots.pop(); // remove it from pending
      } // free the lock
      
      // check if system is still in the first attraction basin
      int reachedSST = identifyAttractionBasin(snap);
      
      // if not, request simul to proceed to next run
      if (reachedSST != startSteadyState)
      {
        string strtime = to_string(snap.time-0.5*escapeTimePrecision);
        
        // print to user for a follow-up
        LOG("Has Left Initial Attraction Basin at time " + strtime);
        
        // store escape time, taken at the bin center of interval [time - exitTimePrecision ; time]
        if (!runsTreated.contains(snap.run)) // store just once
        {
          //escapeTimes.setUnchecked(snap.run, snap.time - 0.5*escapeTimePrecision);
          float centerTime = snap.time - 0.5*escapeTimePrecision;
          //escapes.add({centerTime, startSteadyState, reachedSST});
          escapes.setUnchecked(snap.run, {centerTime, startSteadyState, reachedSST});
          runsTreated.add(snap.run);
          clearSnapshots(snap.run); // useless to treat following snapshots of current run, so clear them
        }
        
        // request a new run to simulation thread
        if (!debug) 
          simul.requestProceedingToNextRun(snap.run);
      }
      
      // if current time is greater than simulation time and still no escape is detected, keep track of it
      if (snap.time + 2*simul.dt->floatValue() > simul.totalTime->floatValue()) // I use 2*dt just to make sure to go below totalTime, I'm scared of rounded stuff here and there.
      {
        LOG("No escape detected");
        escapes.setUnchecked(snap.run, {-1., startSteadyState, startSteadyState});
        //escapes.add({-1., startSteadyState, reachedSST});
      }
            
    } // end while over pending snapshots
    
    if (runsTreated.contains(simul.nRuns-1))
    {
      writeResultsToFile();
    }
    
  } // outter thread while loop
}



int FirstEscapeTimeWorker::identifyAttractionBasin(const Snapshot&  snap)
{
  //cout << "FirstEscapeTime::identifyAttractionBasin()" << endl;
  ConcentrationGrid cg = snap.concgrid;
  
  // set entities to the concentration corresponding to input argument
  for (auto & ent : entities)
  {
    pair<int, int> p = make_pair(patchid, ent->idSAT);
    //if (!cg.contains(p))
    float input_conc = cg[p];
    ent->concent.setUnchecked(patchid, input_conc);
  }
  
  
  //cout << "start conc : ";
  //for (auto & ent : entities)
  //  cout << ent->concent.getUnchecked(patchid) << " ";
  //cout << endl;
  
  
  // deterministic dynamics of the system until a stationnary state is reached
  float distance = 1000.;
  int timeout = dt_study * 50000;
  float t = 0.;
  int count = 0;
  bool delay = true; // I require the deterministic search to run a minimum amount of time
  // otherwise, too close from an unstable steady state, variation might be too small
  while (distance>precision || delay)
  {
    count++;
    t += dt_study;
    if (t>100.) // free the boolean delay
      delay = false;
    if (t>timeout)
      break;
    // deterministic traj
    kinetics->SteppingReactionRates(reactions, dt_study, patchid, false);
    kinetics->SteppingInflowOutflowRates(entities, dt_study, patchid);
    
    // update concentration values of entities
    for (auto & ent : entities)
    {
      ent->refresh();
    }
    
    // calculate variation in last dt
    distance = 0.;
    for (auto & ent : entities)
    {
      float deltaC = ent->concent.getUnchecked(patchid)-ent->previousConcent.getUnchecked(patchid);
      distance += deltaC*deltaC;
    }
    distance = sqrt(distance);
    
  } // end while
  
  
  
  cout << "FirstEscapeTimeWorker::identifyAttractionBasin() end conc : ";
  for (auto & ent : entities)
    cout << ent->concent.getUnchecked(patchid) << " ";
  cout << endl;
  
  
  // determine in which steady state the system is
  int reachedSST = -1;
  float dmin = 1000.;
  count = 0;
  for (auto & sst : simul.steadyStatesList->arraySteadyStates)
  {
    //if (!sst.isStable)
    //  continue;
    float d = distanceFromSteadyState(sst.state);
    //cout << "candidate sst : " << endl;
    //simul.steadyStatesList->printOneSteadyState(sst);
    //cout << "is stable ? --> " << sst.isStable << endl;
    //cout << "distance = " << d << endl;
    if (d<dmin)
    {
      dmin = d;
      reachedSST = count;
    }
    count++;
  }
  
  //cout << "run = " << snap.run << ". t_simul = " << snap.time << endl;
  //cout << "startSST = " << startSteadyState << " vs reachedSST " << reachedSST << endl;
  
  if (reachedSST<0)
    LOGWARNING("Could not determine in which steady state the system ended.");
  
  //cout << "reached sst (";
  //for (auto & ent : entities)
  //  cout << ent->concent.getUnchecked(patchid) << " ";
  //cout << ")" << endl;
  
  
  return reachedSST;
}



float FirstEscapeTimeWorker::distanceFromSteadyState(State state)
{
  float d = 0.;
  for (auto & p : state)
  {
    int entID = p.first->idSAT;
    SimEntity * se = getSimEntityForID(entID);
    float dc = se->concent.getUnchecked(patchid) - p.second;
    d += dc*dc;
  }
  d = sqrt(d);
  
  return d;
}

SimEntity * FirstEscapeTimeWorker::getSimEntityForID(const size_t idToFind)
{
  for (auto &se : entities)
  {
    if (se->idSAT == idToFind)
      return se;
  }
  LOGWARNING("Failed to find SimEntity for id " << idToFind);
  return nullptr;
}


void FirstEscapeTimeWorker::writeResultsToFile()
{
  cout << "printResultsToFile()" << endl;
  ofstream outputfile;
  String out = outputfilename + "_srun" + String(to_string(superRun)) + ".csv";
  outputfile.open(out.toStdString(), ofstream::out | ofstream::trunc);

  cout << "writing to file " << out << endl;
  
  outputfile << "Network " << network << "\n" << endl;
  outputfile << "epsilon noise =  " << Settings::getInstance()->epsilonNoise->floatValue() << "\n" << endl;
  outputfile << "<===== RESULTS =====>" << endl;
  outputfile << "startSST,escapeSST,time" << endl;
        
  //int c=-1;
  for (auto & el : escapes)
  {
    outputfile << el.startSteadyState << "," << el.escapeSteadyState << "," << el.time << endl;
  }
}
