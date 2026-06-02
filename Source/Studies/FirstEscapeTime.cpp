#include "FirstEscapeTime.h"
using namespace juce;
// constructor
FirstEscapeTime::FirstEscapeTime() : simul(Simulation::getInstance())
{
  if (simul == nullptr)
    LOGWARNING("SImulation pointer init. to null pointer");
  //worker = new FirstEscapeTimeWorker(*simul);
  simul->addAsyncSimulationListener(this);
  copyReactionNetwork();
}

//SimulationUI::SimulationUI() : ShapeShifterContentComponent(Simulation::getInstance()->niceName),
//                 simul(Simulation::getInstance())

// destructor
FirstEscapeTime::~FirstEscapeTime()
{
  simul->removeAsyncSimulationListener(this);
  //simul->removeAsyncContainerListener(this);
}


void FirstEscapeTime::escapeDetected(const Escape& e)
{
    const juce::ScopedLock sl(pendingEscapesLock);
    pendingEscapes.add(e);
}


void FirstEscapeTime::copyReactionNetwork()
{
  crn.entities.clear();
  crn.reactions.clear();
    
  // fill entity array with copies of the ones present in the simulation instance
  // careful, they should not be modified while this study is being called, so I'll probably have to pause the Simulation thread ?
  // or make sure to update the simentity concentration value with the one
  for (auto & ent : simul->entities)
    crn.entities.add(ent->clone().release());
  
  for (auto & ent : crn.entities)
    ent->entity = nullptr; // just make sure this copied SimEntity will not interfere with Entity object
  
  for (auto & r : simul->reactions)
  {
    Array<SimEntity*> reactants;
    Array<SimEntity*> products;
    for (auto & e : r->reactants)
    {
      reactants.add(simul->entities[e->idSAT]);
    }
    for (auto & e : r->products)
    {
      products.add(simul->entities[e->idSAT]);
    }
    SimReaction * copyr = new SimReaction(reactants, products, r->assocRate ,  r->dissocRate,  r->energy);
    crn.reactions.add(copyr);
  }
}


void FirstEscapeTime::setSimulationConfig(std::map<String, String> configs)
{
  for (auto& [key, val] : configs)
  {
    //cout << "key, val : " << key << " " << val << endl;
    juce::var myvar(val);
    //if (key == "output")
    //  networkfile = val;
    if (key == "dt")
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
  simul->concentrationMode->setValue(1); // Stochastic
  GlobalSettings::getInstance()->logAutosave->setValue(false); // autosave pretty annoying in the case of this study
  Settings::getInstance()->printHistoryToFile->setValue(printDynamics2File);
  
  // initialize runs
  PhasePlane::getInstance()->clearAllRuns();
  PhasePlane::getInstance()->nRuns->setValue(nruns);
  PhasePlane::getInstance()->updateEntitiesFromSimu(); // so that all runs have correct initial conditions

  // correct number of threads if they exceed that of the hardware
  if (cores == 0)
  {
    LOGWARNING("Number of cores set to 0, reset its value to default value 1.");
    cores = 1;
  }
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
  simul->setStartConcToSteadyState(simul->entities, startSteadyState+1); // startSteadyState is in [0, Nsteadystates-1], but method expects it to be in [1, Nsteadystates]
  // same for entities belonging to this class
  simul->setStartConcToSteadyState(worker->entities, startSteadyState+1); // I should avoid this
  
  // synchronize runs of phase plane with simul
  PhasePlane::getInstance()->updateEntitiesFromSimu();
  
  // just in case
  //Simulation::getInstance()->generateSimFromUserList();
  
  // debug
  //simul->steadyStatesList->printSteadyStates();
  
  // initialize runs
  //PhasePlane::getInstance()->clearAllRuns();
  //PhasePlane::getInstance()->nRuns->setValue(nruns);
  //PhasePlane::getInstance()->updateEntitiesFromSimu(); // so that all runs have correct initial conditions
  
  // start worker thread
  //worker->reset();
  //worker->startThread(); // start the worker thread
  
  // start simulation
  PhasePlane::getInstance()->startRuns(); // start simulation thread
  
}

/*
void FirstEscapeTime::printResultsToFile()
{
  cout << "printResultsToFile()" << endl;
  ofstream outputfile;
  String out = outputfilename + "_srun" + String(to_string(superRun)) + ".csv";
  outputfile.open(out.toStdString(), ofstream::out | ofstream::trunc);

  cout << "writing to file " << out << endl;
  
  outputfile << "Network " << networkfile << "\n" << endl;
  outputfile << "epsilon noise =  " << Settings::getInstance()->epsilonNoise->floatValue() << "\n" << endl;
        
  int c=-1;
  for (auto & t : escapeTimes)
  {
    c++;
    string newline = ((c == (escapeTimes.size()-1) ) ? "" : "\n");
    outputfile << t << newline;
  }
  outputfile << endl;
}
*/


void FirstEscapeTime::newMessage(const Simulation::SimulationEvent &ev)
{
  switch (ev.type)
  {
    case Simulation::SimulationEvent::UPDATEPARAMS:
    {
    }
  break;
      
    case Simulation::SimulationEvent::WILL_START:
    {
      //worker->startThread(); // start the worker thread
    }
  break;

    case Simulation::SimulationEvent::STARTED:
    {
      // test in which attraction basin in the system
    }
  break;

    case Simulation::SimulationEvent::NEWSTEP:
    {
      // test in which attraction basin in the system
      ConcentrationGrid cg = ev.entityValues;
      float time = simul->dt->floatValue() * static_cast<float>(ev.nStep);
      //cout << "SimulationEvent::NEWSTEP at step " << ev.nStep << " --> time = " << time << endl;
      if (!simul->redrawRun && !simul->redrawPatch)
      {
        FirstEscapeTimeJob * newJob = new FirstEscapeTimeJob(*this, crn, cg, escapes, ev.run, ev.time, exitTimePrecision, startSteadyState);
        pool->addJob(newJob, true);
      }
        //worker->submitSnapshot(cg, time, ev.run);
    }
  break;
      
    case Simulation::SimulationEvent::NEWRUN:
    {
      //worker->clearSnapshots(); // in principle should already be fine, but just to make sure
    }
  break;

    case Simulation::SimulationEvent::FINISHED:
    {
      //worker->signalThreadShouldExit(); // tell the worker to exit thread
      //escapeTimes = worker->escapeTimes;
      //printResultsToFile();
    }
      
  } // end switch
}
