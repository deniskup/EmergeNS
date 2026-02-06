#include "FirstExitTime.h"

// constructor
FirstExitTime::FirstExitTime() : simul(Simulation::getInstance())
{
  
}

//SimulationUI::SimulationUI() : ShapeShifterContentComponent(Simulation::getInstance()->niceName),
//                 simul(Simulation::getInstance())

// destructor
FirstExitTime::~FirstExitTime()
{
}


void FirstExitTime::reset()
{
  entities.clear();
  reactions.clear();
  

  
  // fill entity array with copies of the ones present in the simulation instance
  // careful, they should not be modified while this study is being called, so I'll probably have to pause the Simulation thread ?
  // or make sure to update the simentity concentration value with the one
  for (auto & ent : simul->entities)
    entities.add(ent->clone().release());
  
  for (auto & ent : entities)
    ent->entity = nullptr; // just make sure this copied SimEntity will not interfere with Entity object
  
  for (auto & r : simul->reactions)
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


void FirstExitTime::setSimulationConfig(std::map<String, String> configs)
{
  for (auto& [key, val] : configs)
  {
    //cout << "key, val : " << key << " " << val << endl;
    juce::var myvar(val);
    if (key == "network")
      networkfile = val;
    else if (key == "dt")
      simul->dt->setValue(atof(val.toUTF8()));
    //else if (key == "dtbis") dtbis = atof(val.c_str());
    else if (key == "totalTime")
      simul->totalTime->setValue(atof(val.toUTF8()));
    else if (key == "exitTimePrecision")
      precision = atof(val.toUTF8());
    else if (key == "epsilonNoise")
      Settings::getInstance()->volume->setValue(-2.*log10(atof(val.toUTF8())));
    else if (key == "nRuns")
      nruns = atoi(val.toUTF8());
    else if (key == "fixedSeed")
      fixedSeed = atoi(val.toUTF8());
    else if (key == "seed")
      seed = atoi(val.toUTF8());
    //else if (key == "nstepbis") nstepbis = atoi(val.c_str());
    //else if (key == "epsilon") epsilon = atof(val.c_str());
    //else if (key == "maxsteps_study") maxsteps_study = atoi(val.c_str());
    else if (key == "outputfilename")
      outputfilename = val;
    //else if (key == "dtsave") dtsave = atof(val.c_str());
    else if (key == "startSteadyState")
      startSteadyState = atoi(val.toUTF8());
    //else if (key == "superRun") superRun = atoi(val.c_str());
  }
  
  // set simulation instance parameters according to those of
  //Simulation::getInstance()->exitTimeStudy = true;
  //Simulation::getInstance()->transitStudy = false;
  Settings::getInstance()->fixedSeed->setValue(fixedSeed);
  Settings::getInstance()->randomSeed->setValue(seed);
  
  /*
  Simulation::getInstance()->dtbis = dtbis;
  Simulation::getInstance()->maxsteps_study = maxsteps_study;
  Simulation::getInstance()->exitTimePrecision = exitTimePrecision;
  Simulation::getInstance()->epsilon = epsilon;
  Simulation::getInstance()->outputfilename = outputfilename;
  Simulation::getInstance()->superRun = superRun;
  */
  
  // additionnal configurations
  simul->autoScale->setValue(true);
  simul->stochasticity->setValue(true);
  //Simulation::getInstance()->noVisu = true;
  
}



// #TODO clarify what is in there 
void FirstExitTime::startStudy()
{
  
  if (simul->isSpace->boolValue())
  {
    LOGWARNING("Cannot perform Exit time study in heterogeneous space. Abort study.");
    return;
  }
  
  /*
  
  if (Simulation::getInstance()->steadyStatesList->arraySteadyStates.size() == 0)
  {
    LOG("should calculate steady states and save the file, for now I just leave the function.");
    return;
  }
  
  // set concentration of entities to the one of steady state
  SteadyState startSST;
  int indexStartSST = -1;
  
  int c=-1;
  for (auto & sst : Simulation::getInstance()->steadyStatesList->arraySteadyStates)
  {
    c++;
    //SteadyStateslist::getInstance()->printOneSteadyState(sst);
    if (sst.isBorder)
      continue;
    
    // choose the steady state A or B dominated
    float totA = 0.;
    for (auto & [ent, c] : sst.state)
    {
      if (c>100)
        break;
      if (ent->name.contains(startSteadyState))
        totA += c;
    }
    //cout << "total A species = " << totA << ". index sst = " << c << endl;
    if (totA > 100) // avoid pathological steady states found
      continue;
    if (totA>0.1)
    {
      startSST = sst;
      indexStartSST = c;
      break;
    }
  }

  indexStartSST = 8;
  
  //cout << "picked sst index " << indexStartSST << endl;
  
  
  // set startConc to this steady state
  if (indexStartSST>=0)
  {
    //SteadyStateslist::getInstance()->printOneSteadyState(startSST);
    Simulation::getInstance()->setConcToSteadyState(indexStartSST+1, true);
    Simulation::getInstance()->startSST = indexStartSST;
    //Simulation::getInstance()->curSST = indexStartSST;
  }
  else
  {
    LOG("Cannot find matching steady state, stop.");
    return;
  }
  // just in case
  Simulation::getInstance()->generateSimFromUserList();
  
  
  
  // init runs
  PhasePlane::getInstance()->clearAllRuns();
  PhasePlane::getInstance()->nRuns->setValue(nRuns);
  PhasePlane::getInstance()->updateEntitiesFromSimu();
  
  // start simulation
  PhasePlane::getInstance()->startRuns();
  
  */
  
}


void FirstExitTime::newMessage(const Simulation::SimulationEvent &ev)
{
  switch (ev.type)
  {
  case Simulation::SimulationEvent::UPDATEPARAMS:
  {
  }
      
  case Simulation::SimulationEvent::WILL_START:
  {
    reset();
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
  }
  break;

  case Simulation::SimulationEvent::FINISHED:
  {
  }
      
  } // end switch
}
/*
void FirstExitTime::newMessage(const ContainerAsyncEvent &e)
{
  if (e.type == ContainerAsyncEvent::EventType::ControllableFeedbackUpdate)
  {
    if (e.targetControllable == simul->autoScale)
    {
      //  maxConcentUI->setVisible(!simul->autoScale->boolValue());
      shouldRepaint = true;
    }
    else if (e.targetControllable == simul->maxConcent)
    {
      shouldRepaint = true;
    }
    else if (e.targetControllable == simul->detectEquilibrium)
    {
      epsilonEqUI->setVisible(simul->detectEquilibrium->boolValue());
      shouldRepaint = true;
    }
  }
}
*/
