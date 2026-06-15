#include "FirstEscapeTime.h"
using namespace juce;
// constructor
FirstEscapeTime::FirstEscapeTime() : simul(Simulation::getInstance())
{
  if (simul == nullptr)
    LOGWARNING("SImulation pointer init. to null pointer");
  //worker = new FirstEscapeTimeWorker(*simul);
  simul->addAsyncSimulationListener(this);
  copyReactionNetworkFromSimu();
}

//SimulationUI::SimulationUI() : ShapeShifterContentComponent(Simulation::getInstance()->niceName),
//                 simul(Simulation::getInstance())

// destructor
FirstEscapeTime::~FirstEscapeTime()
{
  simul->removeAsyncSimulationListener(this);
  //simul->removeAsyncContainerListener(this);
}


void FirstEscapeTime::signalEscapeDetected(const Escape& e)
{
    float t_current = earliestEscape.at(e.run).time;

    if (e.time < t_current) // update earliest escape for current run
    {
      const juce::ScopedLock sl(lock);
      earliestEscape[e.run] = e;
      escapeDetected[e.run] = true;
      escapes.setUnchecked(e.run, e);

      if (pendingJobs.at(e.run)-1 == 0) // last job in current run
      {
        std::string log = "Run " + std::to_string(e.run) + ": escape detected at time " + to_string(e.time);
        LOG(juce::String(log));
        if (!debugMode)
        {
          LOG("Proceeding to next run");
          simul->requestProceedingToNextRun(e.run);
        }
      }
    }

}


void FirstEscapeTime::signalJobFinished(int runID, int startSST)
{ 
  const juce::ScopedLock sl(lock);
  pendingJobs[runID]--; 

  //cout << "signalJobFinished() for run " << runID << endl;
  //cout << "simu finished ? -> " << simuHasFinished.load() << endl;
  //cout << "pending jobs : " << endl;
  //  for (auto & [key, val] : pendingJobs)
  //    cout << "run " << key << " - " << val << " jobs." << endl;


 /* if (runID == 0)
  {
    cout << "-------------" << endl;
    cout << "pending jobs : " << pendingJobs.at(runID) << endl;
    cout << "simu sends messages : " << simuSendsMessages.at(runID) << endl;
    cout << "simu has finished : " << simuHasFinished.load() << endl;
    cout << "escape detected : " << escapeDetected.at(runID) << endl;
    cout << endl;
  }
  */

  // if no escape has been detected for current run and this was the last job of the run, store empty escape
  //cout << "in run " << runID << ". remaining jobs in run : " << pendingJobs.at(runID) << ". More messages to come : " << simuSendsMessages.at(runID) << ". escape ? " << escapeDetected.at(runID) << endl;
  if (pendingJobs.at(runID) == 0 && !simuSendsMessages.at(runID) && !escapeDetected.at(runID))
  {
    Escape noescape = {runID, -1., startSST, startSST};
    escapes.setUnchecked(runID, noescape);
    LOG("Run " + juce::String(runID) + ": no escape detected");
  }

  // following is to decide whether should print results to file (i.e. this was the last job)
  // conditions for being the last job ever submitted
  // - (i) belonging to the last run
  // - (ii) an escape was detected in the last run and no more job (last run) is running
  // - (iii) no escape detected in the last run and no more messages being sent by simulation and no more jobs remaining
  // (i) and ((ii) or (iii))

  // count total number of remaining jobs
  int remaining = 0;
  for (auto & [run, jobs] : pendingJobs)
  {
    remaining += jobs;
  }



  bool i = (runID == nruns-1);
  bool ii = (escapeDetected.at(nruns-1) && remaining == 0);
  bool iii = (!escapeDetected.at(nruns-1) && !simuSendsMessages.at(nruns-1) && remaining == 0);
  bool lastJobEver = (i && (ii || iii));

  //cout << "in run " << runID << ". remaining jobs : " << remaining << ". More messages to come (last run) : " << simuSendsMessages.at(nruns-1) << ". escape (last run) ? " << escapeDetected.at(nruns-1);
  //cout << ". lastJobEver : " << lastJobEver << endl;

  if (!lastJobEver)
    return;

  printResultsToFile();


  // first check whether this job was the last job ever

  


  // simu no longer sends message to current run or an escape has already been detected
  //if (simuSendsMessages.at(nruns-1) || escapeDetected.at(nruns-1))
  //  return;
    
  // count total number of remaining jobs
  //int remaining = 0;
  //for (auto & [run, jobs] : pendingJobs)
 // {
 //   remaining += jobs;
 // }
    

  

  // print results to file if simu has finished and no more job is pending
  //if (remaining == 0 && !resultsWritten.exchange(true))
  //{
  //printResultsToFile();
  //}

}

void FirstEscapeTime::copyReactionNetworkFromSimu()
{
  crn.entities.clear();
  crn.reactions.clear();

  juce::Array<SimEntity*> copy_simEntities;
  juce::Array<SimReaction*> copy_simReactions;
    
  // fill entity array with copies of the ones present in the simulation instance
  // careful, they should not be modified while this study is being called, so I'll probably have to pause the Simulation thread ?
  // or make sure to update the simentity concentration value with the one
  for (auto & ent : simul->entities)
    copy_simEntities.add(ent->clone().release());
  
  for (auto & ent : copy_simEntities)
    ent->entity = nullptr; // just make sure this copied SimEntity will not interfere with Entity object
  
  for (auto & r : simul->reactions)
  {
    Array<SimEntity*> reactants;
    Array<SimEntity*> products;
    for (auto & e : r->reactants)
    {
      reactants.add(copy_simEntities[e->idSAT]);
    }
    for (auto & e : r->products)
    {
      products.add(copy_simEntities[e->idSAT]);
    }
    SimReaction * copyr = new SimReaction(reactants, products, r->assocRate ,  r->dissocRate,  r->energy);
    copy_simReactions.add(copyr);
  }

  for (auto & e : copy_simEntities)
    crn.entities.add(e);
  
  for (auto & r : copy_simReactions)
    crn.reactions.add(r);

  // copy steady states
  crn.arraySteadyStates.clear();
  for (auto & sst : simul->steadyStatesList->arraySteadyStates)
  {
    crn.arraySteadyStates.add(sst);    
  }
}


void FirstEscapeTime::setSimulationConfig(std::map<String, String> configs)
{
  for (auto& [key, val] : configs)
  {
    //cout << "key, val : " << key << " " << val << endl;
    juce::var myvar(val);
    if (key == "output")
      outputfilename = val;
    else if (key == "network")
      network = val;
    else if (key == "dt")
      simul->dt->setValue(atof(val.toUTF8()));
    else if (key == "dt_study")
      dt_study = atof(val.toUTF8());
    else if (key == "totalTime")
      simul->totalTime->setValue(atof(val.toUTF8()));
    else if (key == "precision")
      precision = atof(val.toUTF8());
    else if (key == "exitTimePrecision")
      exitTimePrecision = atof(val.toUTF8());
    else if (key == "epsilonNoise")
      Settings::getInstance()->volume->setValue(-2.*log10(atof(val.toUTF8())));
    else if (key == "nRuns")
      nruns = atoi(val.toUTF8());
    else if (key == "fixedSeed")
      fixedSeed = atoi(val.toUTF8());
    else if (key == "seed")
      seed = atoi(val.toUTF8());
    else if (key == "startSteadyState")
      startSteadyState = atoi(val.toUTF8());
    else if (key == "dynamics2file")
      printDynamics2File = atoi(val.toUTF8());
    else if (key == "debug")
      debugMode = atoi(val.toUTF8());
    else if (key == "superRun")
      superRun = atoi(val.toUTF8());
    else if (key == "cores")
      cores = atoi(val.toUTF8());
  }
  printDynamics2File = bool(printDynamics2File);
  
  // set simulation instance parameters according to those of config file
  
  // seeds
  Settings::getInstance()->fixedSeed->setValue(fixedSeed);
  Settings::getInstance()->randomSeed->setValue(seed);
  
  // number of checkpoints
  if (exitTimePrecision == 0.)
  {
    LOGWARNING("Exit time precision is 0., reset its value to default value 10.");
    exitTimePrecision = 10.;
  }
  int ncheckpoints = simul->totalTime->floatValue() / exitTimePrecision;
  simul->pointsDrawn->setValue(ncheckpoints);
  
  // additionnal configurations
  simul->autoScale->setValue(true);
  simul->concentrationMode->setValueWithData(1); // Stochastic
  GlobalSettings::getInstance()->logAutosave->setValue(false); // autosave pretty annoying in the case of this study
  Settings::getInstance()->printHistoryToFile->setValue(printDynamics2File);
  
  // initialize runs
  PhasePlane::getInstance()->clearAllRuns();
  PhasePlane::getInstance()->nRuns->setValue(nruns);
  PhasePlane::getInstance()->updateEntitiesFromSimu(); // so that all runs have correct initial conditions

  // set all entities in simu drawable
  for (auto& ent : simul->entities)
  {
    if (ent->entity != nullptr)
    {
      ent->entity->draw->setValue(true);
    }
    else
    {
      LOGWARNING("Entity in SimEntity " + ent->name + " is null. Stop.");
      return;
    }
  }

  // cores
  if (cores == 0)
  {
    LOGWARNING("Number of cores set to 0, reset its value to default value 1.");
    cores = 1;
  }
  // correct number of threads if they exceed that of the hardware
  int maxCores = juce::SystemStats::getNumCpus(); 
  cores = std::min(cores, maxCores);

  // if cores is set to negative integer, it means that the user wants to use all available cores
  if (cores < 0)
    cores = maxCores;
  
  // init the threadpool
  pool = new juce::ThreadPool(cores);
  //worker->setSimulation(*simul);
  //worker->reset(); // will copy some simulation thread parameters
  //worker->setConfig(configs); // will copy some input config file parameters

  // store some parameters that will be passed to jobs
  studyParams.precision = precision;
  studyParams.escapeTimePrecision = exitTimePrecision;
  studyParams.dt_study = dt_study;
  studyParams.startSteadyState = startSteadyState;

  simuHasFinished.store(false);
  
  // force simulation thread to not store dynamics 
  simul->lightMemory.store(!printDynamics2File, std::memory_order_release);
}



// #TODO clarify what is in there
void FirstEscapeTime::startStudy()
{
  if (simul->isSpace->boolValue())
  {
    LOGWARNING("Cannot perform Exit time study in heterogeneous space. Abort study.");
    return;
  }
  
  if (simul->steadyStatesList->arraySteadyStates.size() == 0)
  {
    LOGWARNING("No steady state found, cannot perform first exit time study.");
    return;
  }
  
  if (startSteadyState >= simul->steadyStatesList->arraySteadyStates.size())
  {
    LOGWARNING("Start steady state index greater than total umber of steady state. Exit.");
    return;
  }  
  // set concentration of entities in simul to the one of initial steady state
  simul->setStartConcToSteadyState(simul->entities, startSteadyState+1, true); // startSteadyState is in [0, Nsteadystates-1], but method expects it to be in [1, Nsteadystates]
  // same for entities belonging to this class
  
  // synchronize runs of phase plane with simul
  PhasePlane::getInstance()->updateEntitiesFromSimu();

  cout << "Nentities in simu : " << simul->entities.size() << endl;

  // start simulation
  PhasePlane::getInstance()->startRuns(); // start simulation thread
  
}


void FirstEscapeTime::printResultsToFile()
{
  //cout << "printResultsToFile()" << endl;
  //cout << "N escapes = " << escapes.size() << endl;
  ofstream outputfile;
  String out = outputfilename + "_srun" + String(to_string(superRun)) + ".csv";
  outputfile.open(out.toStdString(), ofstream::out | ofstream::trunc);

  cout << "writing to file " << out << endl;
  
  outputfile << "Network " << network << "\n" << endl;
  outputfile << "epsilon noise =  " << Settings::getInstance()->epsilonNoise->floatValue() << endl;
  //outputfile << "Dynamics history in simu thread =  " << Simulation::getInstance()->dynHistory->concentHistory.size() << "\n" << endl;
  outputfile << "<===== RESULTS =====>" << endl;
  outputfile << "run,startSST,escapeSST,time" << endl;
        
  int c=-1;
  for (auto & e : escapes)
  {
    c++;
    string newline = ((c == (escapes.size()-1) ) ? "" : "\n");
    outputfile << e.run << "," << e.startSteadyState << "," << e.escapeSteadyState << "," << e.time << newline;
  }
  outputfile << endl;
}


/*
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
*/


void FirstEscapeTime::newMessage(const Simulation::SimulationEvent &ev)
{
  if (simul->redrawPatch || simul->redrawRun)
    return;

  switch (ev.type)
  {
    case Simulation::SimulationEvent::UPDATEPARAMS:
    {
    }
  break;
      
    case Simulation::SimulationEvent::WILL_START:
    {
      const juce::ScopedLock sl(lock);
      simuSendsMessages.clear();
      for (int r=0; r<nruns; r++)
        simuSendsMessages[r] = true;
      runBeingTreated.store(0);
      escapeDetected.clear();
      for (int r=0; r<nruns; r++)
        escapeDetected[r] = false;
      earliestEscape.clear();
      earliestEscape[0] = {0, std::numeric_limits<float>::max(), startSteadyState, -1};
      pendingJobs.clear();
      pendingJobs[0] = 0;
      escapes.clear();
      escapes.insertMultiple(0, {-1, -1., -1, -1}, nruns);
    }
  break;

    case Simulation::SimulationEvent::STARTED:
    {
    }
  break;

    case Simulation::SimulationEvent::NEWSTEP:
    {
      const juce::ScopedLock sl(lock);
      // test in which attraction basin in the system
      ConcentrationGrid cg = ev.entityValues;
      float time = simul->dt->floatValue() * static_cast<float>(ev.nStep);
      //cout << "SimulationEvent::NEWSTEP at step " << ev.nStep << " --> time = " << time << endl;
      messageCounters[ev.run]++;

      //cout << ev.run << " : " << messageCounters.at(ev.run) << " ; " << simul->pointsDrawn->intValue() << " : " << time << endl;
      if (messageCounters.at(ev.run) == simul->pointsDrawn->intValue())
      {
        simuSendsMessages[ev.run] = false;
      }

      if (escapeDetected.at(ev.run) == false) // if a previous job detected an escape, do not submit more jobs
      {
        CRNSimulation copyCRN(crn);
        FirstEscapeTimeJob * newJob = new FirstEscapeTimeJob(*this, copyCRN, cg, ev.run, time, studyParams);
        pool->addJob(newJob, true);
        pendingJobs[ev.run]++;
        if (pool->getNumJobs()>1000)
        {
          juce::String njobs(std::to_string(pool->getNumJobs()));
          LOGWARNING("Many jobs queuing or running : " + njobs);
        }
      }

      
    }
  break;
      
    case Simulation::SimulationEvent::NEWRUN:
    {
      const juce::ScopedLock sl(lock);
      //simuSendsMessages[ev.run] = true;
      escapeDetected[ev.run] = false;
      earliestEscape[ev.run] = {ev.run, std::numeric_limits<float>::max(), startSteadyState, -1};
      pendingJobs[ev.run] = 0;
    }
  break;

    case Simulation::SimulationEvent::FINISHED:
    {
      const juce::ScopedLock sl(lock);
      simuHasFinished.store(true);
    }
      
  } // end switch
}
