#include "FirstExitTimeWorker.h"


void FirstExitTimeWorker::setConfig(map<String, String> configs)
{
  for (auto& [key, val] : configs)
  {
    //cout << "key, val : " << key << " " << val << endl;
    juce::var myvar(val);
    if (key == "dt_study")
      dt_study = atof(val.toUTF8());
    else if (key == "precision")
      precision = atof(val.toUTF8());
    else if (key == "exitTimePrecision")
      escapeTimePrecision = atof(val.toUTF8());
    else if (key == "startSteadyState")
      startSteadyState = atoi(val.toUTF8());
  }
}



void FirstExitTimeWorker::reset()
{
  cout << "FirstExitTimeWorker::reset()" << endl;
  entities.clear();
  reactions.clear();
  
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
  
  cout << "--- FirstExitTime::reset() ---" << endl;
  cout << "--- SimEntity list : " << endl;
  for (auto & ent :entities)
    cout << "\t" << ent->name << endl;
  cout << "--- SimReaction list : " << endl;
  for (auto & r :reactions)
  {
    cout << r->name << endl;
    cout << "reactants : " << endl;
    for (auto& e :r->reactants)
      cout << "\t" << e->name << endl;
    cout << "products : " << endl;
    for (auto& e :r->products)
      cout << "\t" << e->name << endl;
  }
  
}


void FirstExitTimeWorker::submitSnapshot(const ConcentrationGrid& cg, float time)
{
    const juce::ScopedLock sl(dataLock);
    pendingSnapshots.push({cg, time});

    workAvailable.signal(); // wake up worker thread
}

void FirstExitTimeWorker::clearSnapshots()
{
  { // empty the queue with the lock
    const juce::ScopedLock sl(dataLock);
    while (!pendingSnapshots.empty())
      pendingSnapshots.pop();
  } // free the lock
  signalThreadShouldExit();
  workAvailable.signal(); // wake the thread to make it exit
}



void FirstExitTimeWorker::run()
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
        string strtime = to_string(snap.time); // find a way to know time of simulation in here and tell simulation to move to next run
        
        // print to user for a follow-up
        LOG("Has Left Initial Attraction Basin at time " + strtime);
        
        // store escape time, taken at the bin center of interval [time - exitTimePrecision ; time]
        if (!hasStoredEscapeTime)
          escapeTimes.add(snap.time - 0.5*escapeTimePrecision);
        
        // request a new run to simulation thread
        simul.requestToMoveToNextRun();
      }
    }
    
    }
}




int FirstExitTimeWorker::identifyAttractionBasin(const Snapshot&  snap)
{
  ConcentrationGrid cg = snap.concgrid;
  
  // set entities to the concentration corresponding to input argument
  for (auto & ent : entities)
  {
    pair<int, int> p = make_pair(patchid, ent->idSAT);
    //if (!cg.contains(p))
    float input_conc = cg[p];
    ent->concent = input_conc;
  }
  
  // deterministic dynamics of the system until a stationnary state is reached
  float distance = 1000.;
  int timeout = 10000;
  int c = 0;
  while (distance<precision && c<timeout)
  {
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
  
  
  // determine in which steady state the system is
  int reachedSST = -1;
  float dmin = 1000.;
  c = 0;
  for (auto & sst : simul.steadyStatesList->arraySteadyStates)
  {
    float d = distanceFromSteadyState(sst.state);
    if (d<dmin)
      reachedSST = c;
    c++;
  }
  
  cout << "FirstExitTime::identifyAttraxctionBasin()" << endl;
  cout << "startSST = " << startSteadyState << " vs reahcedSST " << reachedSST << endl;
  
  if (reachedSST<0)
    LOGWARNING("Could not determine in which steady state the system ended.");
  
  // check if the system left initial attraction basin
  if (reachedSST != startSteadyState)
  {
    string strtime = to_string(snap.time); // find a way to know time of simulation in here and tell simulation to move to next run
    
    // print to user for a follow-up
    LOG("Has Left Initial Attraction Basin at time " + strtime);
    
    // store escape time, taken at the bin center of interval [time - exitTimePrecision ; time]
    escapeTimes.add(snap.time - 0.5*escapeTimePrecision);
    
    // request a new run to simulation thread
    simul.requestToMoveToNextRun();
  }
  
  // if current time is greater than simulation total time and still no escape is detected, keep track of it
  if (snap.time + 2*simul.dt->floatValue() > simul.totalTime->floatValue()) // I use 2*dt just to make sure to go below totalTime, I'm scared of rounded stuff here and there.
  {
    LOG("No escape detected");
    escapeTimes.add(-1.);
  }
  
  return reachedSST;
}



float FirstExitTimeWorker::distanceFromSteadyState(State state)
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

SimEntity * FirstExitTimeWorker::getSimEntityForID(const size_t idToFind)
{
  for (auto &se : entities)
  {
    if (se->idSAT == idToFind)
      return se;
  }
  LOGWARNING("Failed to find SimEntity for id " << idToFind);
  return nullptr;
}
