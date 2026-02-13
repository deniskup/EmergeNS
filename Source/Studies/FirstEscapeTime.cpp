#include "FirstEscapeTime.h"

// constructor
FirstEscapeTime::FirstEscapeTime() : simul(Simulation::getInstance())
{
  cout << "calling creator FirstEscapeTime()" << endl;
  if (simul == nullptr)
    LOGWARNING("SImulation pointer init. to null pointer");
  worker = new FirstEscapeTimeWorker(*simul);
  simul->addAsyncSimulationListener(this);
}

//SimulationUI::SimulationUI() : ShapeShifterContentComponent(Simulation::getInstance()->niceName),
//                 simul(Simulation::getInstance())

// destructor
FirstEscapeTime::~FirstEscapeTime()
{
  simul->removeAsyncSimulationListener(this);
  //simul->removeAsyncContainerListener(this);
}



void FirstEscapeTime::setSimulationConfig(std::map<String, String> configs)
{
  cout << "FirstEscapeTime::setSimulationConfig()" << endl;
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
  cout << "using " << ncheckpoints << " checkpoints" << endl;
  simul->pointsDrawn->setValue(ncheckpoints);
  
  // additionnal configurations
  simul->autoScale->setValue(true);
  simul->stochasticity->setValue(true);
  GlobalSettings::getInstance()->logAutosave->setValue(false); // autosave pretty annoying in the case of this study
  Settings::getInstance()->printHistoryToFile->setValue(printDynamics2File);
  
  // pass reelavnt parameters to the worker
  worker->setConfig(configs);
  
}



// #TODO clarify what is in there
void FirstEscapeTime::startStudy()
{
  cout << "FirstEscapeTime::startStudy()" << endl;
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
  simul->setConcToSteadyState(simul->entities, startSteadyState+1); // startSteadyState is in [0, Nsteadystates-1], but method expects it to be in [1, Nsteadystates]
  // same for entities belonging to this class
  simul->setConcToSteadyState(worker->entities, startSteadyState+1); // I should avoid this
  
  // just in case
  //Simulation::getInstance()->generateSimFromUserList();
  
  // debug
  simul->steadyStatesList->printSteadyStates();
  
  // initialize runs
  PhasePlane::getInstance()->clearAllRuns();
  PhasePlane::getInstance()->nRuns->setValue(nruns);
  PhasePlane::getInstance()->updateEntitiesFromSimu(); // so that all runs have correct initial conditions
  
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
      worker->reset();
      worker->startThread(); // start the worker thread
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
      float time = simul->dt->floatValue() * static_cast<float>(ev.nStep-1);
      //cout << "SimulationEvent::NEWSTEP at step " << ev.nStep << " --> time = " << time << endl;
      if (!simul->redrawRun && !simul->redrawPatch)
        worker->submitSnapshot(cg, time, ev.run);
      //identifyAttractionBasin(cg, time);
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
