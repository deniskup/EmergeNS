#include "FirstExitTime.h"

// constructor
FirstExitTime::FirstExitTime() : simul(Simulation::getInstance())
{
  kinetics = new KineticLaw(false, 0.); // input parameters are for stochasticity, not relevant in this study
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
    else if (key == "outputfilename")
      outputfilename = val;
    else if (key == "startSteadyState")
      startSteadyState = atoi(val.toUTF8());
    else if (key == "superRun")
      superRun = atoi(val.toUTF8());
  }
  
  // set simulation instance parameters according to those of
  
  // seeds
  Settings::getInstance()->fixedSeed->setValue(fixedSeed);
  Settings::getInstance()->randomSeed->setValue(seed);
  
  // number of checkpoints
  if (exitTimePrecision == 0.)
  {
    LOGWARNING("Exit time precision set to 0., reset its value to default value 10.");
    exitTimePrecision = 10.;
  }
  int ncheckpoints = simul->totalTime->floatValue() / exitTimePrecision;
  
  
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
  simul->setConcToSteadyState(entities, startSteadyState+1); // I should avoid this
  
  // just in case
  //Simulation::getInstance()->generateSimFromUserList();
  
  
  // initialize runs
  PhasePlane::getInstance()->clearAllRuns();
  PhasePlane::getInstance()->nRuns->setValue(nruns);
  PhasePlane::getInstance()->updateEntitiesFromSimu(); // so that all runs have correct initial conditions
  
  // start simulation
  PhasePlane::getInstance()->startRuns(); // start simulation thread
  
}


/*
void FirstExitTime::setConcToSteadyState(int id)
{
  if (id < 1)
  {
    LOGWARNING("Cannot set concentrations to steady state index < 1");
    return;
  }
  State st = simul->steadyStatesList->arraySteadyStates[id-1].state; // retrieve steady state concent from simul
  int ident = 0;
  for (auto ent : entities)
  {
    float conc = ss.state[ident].second;
    ent->concent = conc;
    ident++;
    if (ent->entity != nullptr)
      ent->entity->concent->setValue(conc);
  }
}
*/


int FirstExitTime::identifyAttractionBasin(ConcentrationGrid & cg, float time)
{
  // desactivate noise in Simulation !!
  
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
  for (auto & sst : simul->steadyStatesList->arraySteadyStates)
  {
    float d = distanceFromSteadyState(sst.state);
    if (d<dmin)
      reachedSST = c;
    c++;
  }
  
  if (reachedSST<0)
    LOGWARNING("Could not determine in which steady state the system ended.");
  
  // check if the system left initial attraction basin
  if (reachedSST != startSteadyState)
  {
    string strtime = to_string(time); // find a way to know time of simulation in here and tell simulation to move to next run
    
    // print to user for a follow-up
    LOG("Has Left Initial Attraction Basin at time " + strtime);
    
    // store escape time, taken at the bin center of interval [time - exitTimePrecision ; time]
    escapeTimes.add(time - 0.5*exitTimePrecision);
    
    // request a new run to simulation thread
    simul->requestToMoveToNextRun();
  }
  
  // if current time is greater than simulation time and still no escape is detected, keep track of it
  if (time + 2*simul->dt->floatValue() > simul->totalTime->floatValue()) // I use 2*dt just to make sure to go below totalTime, I'm scared of rounded stuff here and there.
  {
    LOG("No escape detected");
    escapeTimes.add(-1.);
  }
  
  return reachedSST;
}



float FirstExitTime::distanceFromSteadyState(State state)
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


SimEntity * FirstExitTime::getSimEntityForID(const size_t idToFind)
{
  for (auto &se : entities)
  {
    if (se->idSAT == idToFind)
      return se;
  }
  LOGWARNING("Failed to find SimEntity for id " << idToFind);
  return nullptr;
}



void FirstExitTime::printResultsToFile()
{
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
    ConcentrationGrid cg = ev.entityValues;
    float time = simul->dt->floatValue() * ev.nStep;
    identifyAttractionBasin(cg, time);
  }
  break;

  case Simulation::SimulationEvent::FINISHED:
  {
    printResultsToFile();
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
