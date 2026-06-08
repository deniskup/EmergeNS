#include "FirstEscapeTimeJob.h"
#include "FirstEscapeTime.h"
using namespace juce;

/*void FirstEscapeTimeJob::setConfig(map<String, String> configs)
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
    else if (key == "superRun")
      superRun = atoi(val.toUTF8());
  }
}
*/


/*
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
*/


/*void FirstEscapeTimeWorker::run()
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
        runsTreated.add(snap.run);
        //escapes.add({-1., startSteadyState, reachedSST});
      }
            
    } // end while over pending snapshots
    
    if (runsTreated.contains(simul.nRuns-1))
    {
      writeResultsToFile();
      signalThreadShouldExit();
    }
    
  } // outter thread while loop
  
  // request emergens to close
  JUCEApplication::getInstance()->systemRequestedQuit();
  
}

*/


FirstEscapeTimeJob::JobStatus FirstEscapeTimeJob::runJob()
{
  // check if system is still in the first attraction basin
  int reachedSST = identifyAttractionBasin();

  if (reachedSST != startSteadyState && reachedSST >= 0)
  {
    float midtime = time-0.5*escapeTimePrecision;
    Escape e = {run, midtime, startSteadyState, reachedSST};
    listener.signalEscapeDetected(e);
  }

  
/*
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
        runsTreated.add(snap.run);
        //escapes.add({-1., startSteadyState, reachedSST});
      }

      */

  listener.signalJobFinished(run, startSteadyState);
      
  return jobHasFinished; 
  
}





int FirstEscapeTimeJob::identifyAttractionBasin()
{

  // set entities to the concentration corresponding to input argument
  for (auto & ent : crn.entities)
  {
    pair<int, int> p = make_pair(patchid, ent->idSAT);
    float input_conc = snapConc[p];
    ent->concent.setUnchecked(patchid, input_conc);
  }
  
  
  //cout << "start conc : ";
  //for (auto & ent : crn.entities)
  //  cout << ent->concent.getUnchecked(patchid) << " ";
  //cout << endl;
  
  
  // deterministic dynamics of the system until a stationnary state is reached
  float distance = 1000.;
  float timeout = dt * 50000;
  float timedelay = std::min(timeout - 100.f, 1000.f); 
  float t = 0.;
  int count = 0;
  bool delay = true; // I require the deterministic search to run a minimum amount of time
  // otherwise, too close from an unstable steady state, variation might be too small
  while ( (distance>precision || delay) && !shouldExit())
  {
    count++;
    t += dt;
    if (t>1000.) // free the boolean delay
      delay = false;
    if (t>timeout)
      break;
    // deterministic traj
    kinetics->SteppingReactionRates(crn.reactions, dt, patchid, false);
    kinetics->SteppingInflowOutflowRates(crn.entities, dt, patchid);
    
    // update concentration values of entities
    for (auto & ent : crn.entities)
    {
      ent->refresh();
    }
    
    // calculate variation in last dt
    distance = 0.;
    for (auto & ent : crn.entities)
    {
      float deltaC = ent->concent.getUnchecked(patchid)-ent->previousConcent.getUnchecked(patchid);
      distance += deltaC*deltaC;
    }
    distance = sqrt(distance);
    
  } // end while
  
  if (shouldExit())
    return -2;
  
  //cout << "FirstEscapeTimeWorker::identifyAttractionBasin() end conc : ";
  //for (auto & ent : crn.entities)
  //  cout << ent->concent.getUnchecked(patchid) << " ";
  //cout << endl;
  
  
  // determine in which steady state the system is
  int reachedSST = -1;
  float dmin = 1000.;
  count = 0;
  for (auto & sst : crn.arraySteadyStates)
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
  
  //cout << "run = " << run << ". t_simul = " << time << endl;
  //cout << "startSST = " << startSteadyState << " vs reachedSST " << reachedSST << endl;
  
  if (reachedSST<0)
    LOGWARNING("Could not determine in which steady state the system ended.");
  
  //cout << "reached sst (";
  //for (auto & ent : crn.entities)
  //  cout << ent->concent.getUnchecked(patchid) << " ";
  //cout << ")" << endl;
  
  //cout << "end identifyAttractionBasin()" << endl;

  return reachedSST;
}



float FirstEscapeTimeJob::distanceFromSteadyState(State state)
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

SimEntity * FirstEscapeTimeJob::getSimEntityForID(const size_t idToFind)
{
  for (auto &se : crn.entities)
  {
    if (se->idSAT == idToFind)
      return se;
  }
  LOGWARNING("Failed to find SimEntity for id " << idToFind);
  return nullptr;
}


/*
void FirstEscapeTimeJob::writeResultsToFile()
{
  cout << "printResultsToFile()" << endl;
  ofstream outputfile;
  String out = outputfilename + "_srun" + String(to_string(superRun)) + ".csv";
  outputfile.open(out.toStdString(), ofstream::out | ofstream::trunc);

  cout << "writing to file " << out << endl;
  
  outputfile << "Network " << network << "\n" << endl;
  outputfile << "epsilon noise =  " << Settings::getInstance()->epsilonNoise->floatValue() << "\n" << endl;
  outputfile << "Dynamics history in simu thread =  " << Simulation::getInstance()->dynHistory->concentHistory.size() << "\n" << endl;
  outputfile << "<===== RESULTS =====>" << endl;
  outputfile << "startSST,escapeSST,time" << endl;
        
  //int c=-1;
  for (auto & el : escapes)
  {
    outputfile << el.startSteadyState << "," << el.escapeSteadyState << "," << el.time << endl;
  }
}
*/
