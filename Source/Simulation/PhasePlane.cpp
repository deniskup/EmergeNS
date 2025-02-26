// AAARRRGH
//  PhasePlane.cpp
//  EmergeNS - App
//
//  Created by Thomas Kosc on 10/02/2025.
//

#include "PhasePlane.h"

juce_ImplementSingleton(PhasePlane);

Run::Run()
{
  
}

Run::Run(String _name)
{
  name = _name;
  addEtitiesToRun();
}


//Run::Run(OwnedArray<SimEntity*> entities, String _name)
//{
//  name = _name;
//  addEtitiesToRun(entities);
//}



//void Run::addEtitiesToRun(OwnedArray<SimEntity*> entities)
void Run::addEtitiesToRun()
{
  int nent = Simulation::getInstance()->entities.size();
  int n3p = nent/3;
  int rest = nent%3;
  
  // gather entities into 3D points
  for (int i3p=0; i3p<n3p; i3p++)
  {
    int e1 = 3*i3p;
    int e2 = 3*i3p + 1;
    int e3 = 3*i3p + 2;
    String name = Simulation::getInstance()->entities[e1]->name + " | " + Simulation::getInstance()->entities[e2]->name
      + " | " + Simulation::getInstance()->entities[e3]->name;
    //p3p.addPoint3DParameter(name, "Initial concentrations");
    addPoint3DParameter(name, "Initial concentrations");
  }
  // continue with 2D points or float parameter
  if (rest == 2)
  {
    int e1 = nent-2;
    int e2 = nent-1;
    String name = Simulation::getInstance()->entities[e1]->name + " | " + Simulation::getInstance()->entities[e2]->name;
    //cc.addPoint2DParameter(name, "Initial concentrations");
    p2d = addPoint2DParameter(name, "Initial concentrations");
  }
  else if (rest == 1)
  {
    String name = Simulation::getInstance()->entities.getLast()->name;
    //cc.addFloatParameter(name, "Initial concentrations", 0.f, 0.f, 10.f);
    fp = addFloatParameter(name, "Initial concentrations", 0.f, 0.f, 10.f);
  }
  else if (rest == 0)
  {
    
  }
  else cout << "Warning, problem in run initial concentration setting" << endl;
  
}

juce_ImplementSingleton(RunManager);


RunManager::RunManager() : BaseManager("Runs")
{
  //generateTrigger = addTrigger("Generate", "To generate entities");
}

RunManager::~RunManager()
{
  //generateTrigger = addTrigger("Generate", "To generate entities");
}


//////////// default constructor //////////////////////

PhasePlane::PhasePlane() : ControllableContainer("PhasePlane")
{

  showWarningInUI = true;
  saveAndLoadRecursiveData = true;
  includeInRecursiveSave = true;

  
  // trigger buttons
  start = addTrigger("Start", "Start all runs");
  draw = addTrigger("Draw", "Draw all runs");
  startDraw = addTrigger("Start and Draw", "Start and Draw all runs");
  
  // entites defining the 2D plane in which to draw
  xAxis = addTargetParameter("x axis", "x axis", EntityManager::getInstance());
  xAxis->targetType = TargetParameter::CONTAINER;
  //xAxis->maxDefaultSearchLevel = 0;
  //xAxis->setRootContainer(EntityManager::getInstance());

  yAxis = addTargetParameter("y axis", "y axis", EntityManager::getInstance());
  yAxis->targetType = TargetParameter::CONTAINER;
  

  // number of runs
  nRuns = addIntParameter("Number of runs", "Number of runs", 1, 0, 20);
  
  //arun = new ControllableContainer("run 0");
  //arun->saveAndLoadRecursiveData = true;
  //arun->includeInRecursiveSave = true;
  //runs.add(arun);
    
  //for (unsigned int i=0; i<nRuns->intValue(); i++)
  for (unsigned int i=0; i<1; i++)
  {
    String name = "run " + String(to_string(i));
    
    //runs[i] = new ControllableContainer(name);
    //runs[i]->userCanAddControllables = false;
    //runs[i]->isRemovableByUser = true;
    //runs[i]->saveAndLoadRecursiveData = true;
    //addChildControllableContainer(runs[i]);
    //runs[i] = add(arun);

    
    // previous version, showing problems at saving as .ens
    //ControllableContainer * thisrun = new ControllableContainer(name);
    //thisrun->userCanAddControllables = false;
    //thisrun->isRemovableByUser = true;
    //thisrun->saveAndLoadRecursiveData = true;
    //addChildControllableContainer(thisrun);
    //runs.add(thisrun);
    
    Run * thisrun = new Run(name);
    //thisrun->fp = addFloatParameter("fp", "", 1.5);
    //addChildControllableContainer(thisrun->get());
    runs.add(thisrun);

    
  }
  
  //test = new ControllableContainer("TEST");
  //test->addPoint3DParameter("test 3P", "");
  //test->saveAndLoadRecursiveData = true;
  //test->includeInRecursiveSave = true;
  //addChildControllableContainer(test);
  
}





PhasePlane::~PhasePlane()
{
}




void PhasePlane::addEntity(Entity* e)
{
  //FloatParameter* fp = runs->addFloatParameter("Entity " + String(runs->controllables.size() + 1), "Entity " + String(runs->controllables.size() + 1), 0., 0., 100.);
  //if (e != nullptr) fp->setValueFromTarget(e, false);
  //fp->saveValueOnly = false;
  //fp->isRemovableByUser = true;
}

void PhasePlane::addEntitiesToRun(ControllableContainer & cc)
//void PhasePlane::addEntitiesToRun(int krun)
{
  //cc.saveAndLoadRecursiveData = true;
  //saveAndLoadRecursiveData = true;
  //cc.includeInRecursiveSave = true;
  includeInRecursiveSave = true;
  
  int nent = Simulation::getInstance()->entities.size();
  int n3p = nent/3;
  int rest = nent%3;
  
  // gather entities into 3D points
  for (int i3p=0; i3p<n3p; i3p++)
  {
    int e1 = 3*i3p;
    int e2 = 3*i3p + 1;
    int e3 = 3*i3p + 2;
    String name = Simulation::getInstance()->entities[e1]->name + " | " + Simulation::getInstance()->entities[e2]->name
    + " | " + Simulation::getInstance()->entities[e3]->name;
    cc.addPoint3DParameter(name, "Initial concentrations");
  }
  // continue with 2D points or float parameter
  if (rest == 2)
  {
    int e1 = nent-2;
    int e2 = nent-1;
    String name = Simulation::getInstance()->entities[e1]->name + " | " + Simulation::getInstance()->entities[e2]->name;
    cc.addPoint2DParameter(name, "Initial concentrations");
  }
  else if (rest == 1)
  {
    String name = Simulation::getInstance()->entities.getLast()->name;
    cc.addFloatParameter(name, "Initial concentrations", 0.f, 0.f, 10.f);
  }
  else if (rest == 0)
  {
    
  }
  else cout << "Warning, problem in run initial concentration setting" << endl;
  
  
} // end method addEntitiesToRun



void PhasePlane::updateEntitiesInRuns()
{
  for (int i=0; i<runs.size();  i++)
  {
    //r.getControllableContainer()
    runs[i]->clear();
    addEntitiesToRun(*runs[i]);
  }
}


void PhasePlane::onContainerParameterChanged(Parameter *p)
{
  //ControllableContainer::onContainerParameterChanged(p);
  
  if (p == nRuns)
  {
    if (nRuns->intValue()>runs.size()) // must add containers
    {
      for (int k=runs.size(); k<nRuns->intValue(); k++)
      {
        cout << "adding a run" << endl;
        String name = "run " + String(to_string(k));
        ControllableContainer * thisrun = new ControllableContainer(name);
        thisrun->userCanAddControllables = false;
        thisrun->isRemovableByUser = true;
        thisrun->saveAndLoadRecursiveData = true;
        thisrun->includeInRecursiveSave = true;
        addChildControllableContainer(thisrun);
        addEntitiesToRun(*thisrun);

        
        //FloatParameter* fp = thisrun->addFloatParameter("test " + String(thisrun->controllables.size() + 1), "test " + String(thisrun->controllables.size() + 1), 0., 0., 100.);
        //runs.add(thisrun);
      }
    }
    else if (nRuns->intValue()<runs.size())
    {
      while (runs.size()>nRuns->intValue())
      {
        int krm = runs.size()-1;
        removeChildControllableContainer(runs[krm]);
        runs.removeLast(1);
      }
    }
  //cout << "nRuns changed ! new value = " << nRuns->intValue() << ". array size : " << runs.size() << endl;
  }
   
}


void PhasePlane::onContainerTriggerTriggered(Trigger* t)
{
  
  if (t == start)
  {
    cout << "will start runs" << endl;
    startRuns();
  }
  
  else if (t == draw)
  {
    cout << "will start drawing" << endl;
  }
  
  else if (t == startDraw)
  {
    cout << "will start runs and draw them" << endl;
  }
}



void PhasePlane::controllableAdded(Controllable* c)
{
//  int newnRuns = runs.size();
}

void PhasePlane::controllableRemoved(Controllable* c)
{
 // int newnRuns = runs.size();
  cout << "deleted a controllable ! " << endl;
}







void PhasePlane::startRuns()
{
  
  // loop over runs
  int count = -1;
  Array<map<String, float>> initConc;
  for (auto & run : runs)
  {
    count++;
    //cout << "in run #" << count << endl;
   // set entity concentrations to their value in Phase Plane window
    //ControllableContainer * cc = run->getControllableContainerByName("run" + String(to_string(count)));
    juce::Array<juce::WeakReference<Parameter>> allp = run->getAllParameters();
    map<String, float> ic;

    // loop over parameters contained in this run
    // and pass the initial concentrations to actual SimEntities
    for (auto & p : allp)
    {
      if (p->type == Controllable::Type::POINT3D)
      {
        //Point3DParameter pp = (Point3DParameter) p;
        //dynamic_cast<typePoint3DParameter*>(p);
        
        //cout << "\tis point 3D" << endl;
        String pname = p->niceName;
        
        int f1 = pname.indexOf(0, " | ");
        int f2 = pname.indexOf(f1+1, " | ");
        if (f1==-1 || f2==-1){ LOG("error in recovering SimEntity name from Point3D name. Exit"); return;}
        
        String name1 = pname.substring(0, f1);
        String name2 = pname.substring(f1+3, f2);
        String name3 = pname.substring(f2+3, (int) pname.toStdString().size());
        
        Array<var> * arr = p->value.getArray();
        var x = arr[0];
        var y = arr[1];
        var z = arr[2];

        //Simulation::getInstance()->getSimEntityForName(name1)->startConcent = x.operator float();
        //Simulation::getInstance()->getSimEntityForName(name2)->startConcent = y.operator float();
        //Simulation::getInstance()->getSimEntityForName(name3)->startConcent = z.operator float();
        
        if (Simulation::getInstance()->getSimEntityForName(name1) == nullptr) LOG("Can't retrieve entity with name " + name1 + ". Exit.");
        if (Simulation::getInstance()->getSimEntityForName(name2) == nullptr) LOG("Can't retrieve entity with name " + name2 + ". Exit.");
        if (Simulation::getInstance()->getSimEntityForName(name3) == nullptr) LOG("Can't retrieve entity with name " + name3 + ". Exit.");
        
        ic[name1] = x.operator float();
        ic[name2] = y.operator float();
        ic[name3] = z.operator float();
      }
      else if (p->type == Controllable::Type::POINT2D)
      {
        //cout << "\tis point 2D" << endl;
        String pname = p->niceName;
        
        int f1 = pname.indexOf(0, " | ");
        if (f1==-1){ LOG("error in recovering SimEntity name from Point2D name. Exit"); return;}
        
        String name1 = pname.substring(0, f1);
        String name2 = pname.substring(f1+3, (int) pname.toStdString().size());
        
        Array<var> * arr = p->value.getArray();
        var x = arr[0];
        var y = arr[1];

        //Simulation::getInstance()->getSimEntityForName(name1)->startConcent = x.operator float();
        //Simulation::getInstance()->getSimEntityForName(name2)->startConcent = y.operator float();
        
        if (Simulation::getInstance()->getSimEntityForName(name1) == nullptr) LOG("Can't retrieve entity with name " + name1 + ". Exit.");
        if (Simulation::getInstance()->getSimEntityForName(name2) == nullptr) LOG("Can't retrieve entity with name " + name2 + ". Exit.");
        
        ic[name1] = x.operator float();
        ic[name2] = y.operator float();
      }
      else if (p->type == Controllable::Type::FLOAT)
      {
        //cout << "\tis float" << endl;
        String name = p->niceName;
        //Simulation::getInstance()->getSimEntityForName(name)->startConcent = p->floatValue();
        if (Simulation::getInstance()->getSimEntityForName(name) == nullptr) LOG("Can't retrieve entity with name " + name + ". Exit.");
        ic[name] = p->floatValue();
      }
    } // end loop over parameter in run
    
    initConc.add(ic);
    
    if (ic.size() != Simulation::getInstance()->entities.size())
    {
      LOG("Can't start runs as Nentities in Simulation and PhasePlane differ. Exit.");
      cout << "ic.size() = " << ic.size() << " & entities.size() " <<  Simulation::getInstance()->entities.size() << endl;
      return;
    }
    
    // at this stage SimEntities should have their correct init concent value
    // I can run simulation
   // cout << "setting run to " << count << endl;
    //Settings::getInstance()->printHistoryToFile->setValue(true);
    //Simulation::getInstance()->kRun = count;
    //Simulation::getInstance()->start(true);
    //Simulation::getInstance()->run();
    
    // NB : above that does not works. 

    Simulation::getInstance()->startMultipleRuns(initConc);

    
  } // end loop over runs
  
} // end startRuns()


/*
void importJSONData(var data)
{
  
  //clearParams();
  if (data.isVoid())
    return;
  if (data.getDynamicObject() == nullptr)
    return;

  
  if (data.getDynamicObject()->hasProperty("recordConcent"))
    recordConcent = data.getDynamicObject()->getProperty("recordConcent");
  if (data.getDynamicObject()->hasProperty("recordEntity"))
    recordEntity = data.getDynamicObject()->getProperty("recordEntity");
  if (data.getDynamicObject()->hasProperty("recordDrawn"))
    recordDrawn = data.getDynamicObject()->getProperty("recordDrawn");
  if (data.getDynamicObject()->hasProperty("numLevels"))
    numLevels = data.getDynamicObject()->getProperty("numLevels");
  // To move to PACList later
  if (data.getDynamicObject()->hasProperty("PACsGenerated"))
    PACsGenerated = data.getDynamicObject()->getProperty("PACsGenerated");

  // entities
  if (data.getDynamicObject()->hasProperty("entities"))
  {
    if (!data.getDynamicObject()->getProperty("entities").isArray())
    {
      LOGWARNING("Incomplete .ens file, entities of active sim cannot be loaded");
      return;
    }
    auto ents = data.getDynamicObject()->getProperty("entities").getArray();
    for (auto &evar : *ents)
    {
      SimEntity *e = new SimEntity(evar);
      if (e->constructionFailed)
      {
        LOGWARNING("SimEntity construction failed, not added to list");
        delete e;
        continue;
      }
      entities.add(e);
    }
    maxSteps = (int)(totalTime->floatValue() / dt->floatValue());
    maxSteps = jmax(1, maxSteps);
  }

  // reactions
  reactions.clear();
  if (data.getDynamicObject()->hasProperty("reactions"))
  {
    if (!data.getDynamicObject()->getProperty("reactions").isArray())
    {
      LOGWARNING("Incomplete .ens file, reactions of active sim cannot be loaded");
      return;
    }
    auto reacs = data.getDynamicObject()->getProperty("reactions").getArray();
    for (auto &rvar : *reacs)
    {
      SimReaction *r = new SimReaction(rvar);
      if (r->constructionFailed)
      {
        LOGWARNING("SimReaction construction failed, not added to list");
        delete r;
        continue;
      }
      reactions.add(r);
    }
  }

  // PACList
  if (data.getDynamicObject()->hasProperty("pacList"))
  {
    pacList->fromJSONData(data.getDynamicObject()->getProperty("pacList"));
  }

  // precision
  dt->setAttributeInternal("stringDecimals", DT_PRECISION);
  Settings::getInstance()->CACRobustness->setAttributeInternal("stringDecimals", CACROB_PRECISION);
  computeBarriers();
  updateParams();
  
  
}
   */


/*
void afterLoadJSONDataInternal()
{
  
}
*/
