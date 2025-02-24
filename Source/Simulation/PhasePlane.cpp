// AAARRRGH
//  PhasePlane.cpp
//  EmergeNS - App
//
//  Created by Thomas Kosc on 10/02/2025.
//

#include "PhasePlane.h"

juce_ImplementSingleton(PhasePlane);

PhasePlane::PhasePlane() : ControllableContainer("PhasePlane")
//PhasePlane::PhasePlane() : BaseItem("PhasePlane")
{

  showWarningInUI = true;
  
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
  yAxis->maxDefaultSearchLevel = 1;
  
  // number of runs
  nRuns = addIntParameter("Number of runs", "Number of runs", 2, 1, 20);
    
  //for (unsigned int i=0; i<nRuns->intValue(); i++)
  for (unsigned int i=0; i<2; i++)
  {
    String name = "run " + String(to_string(i));
    ControllableContainer * thisrun = new ControllableContainer(name);
    thisrun->userCanAddControllables = false;
    thisrun->isRemovableByUser = true;
    addChildControllableContainer(thisrun);
    runs.add(thisrun);
  }
  
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
  int nent = Simulation::getInstance()->entities.size();
  int n3p = nent/3;
  int rest = nent%3;
  
  cout << "nent = " << nent << endl;

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
  ControllableContainer::onContainerParameterChanged(p);
  
  if (p == nRuns)
  {
    if (nRuns->intValue()>runs.size()) // must add containers
    {
      for (int k=runs.size(); k<nRuns->intValue(); k++)
      {
        String name = "run " + String(to_string(k));
        ControllableContainer * thisrun = new ControllableContainer(name);
        thisrun->userCanAddControllables = false;
        thisrun->isRemovableByUser = true;
        addChildControllableContainer(thisrun);
        
        
        //Point3DParameter * p3d = thisrun->addPoint3DParameter(name, "Initial concentrations");
        
        addEntitiesToRun(*thisrun);

        
        //FloatParameter* fp = thisrun->addFloatParameter("test " + String(thisrun->controllables.size() + 1), "test " + String(thisrun->controllables.size() + 1), 0., 0., 100.);
        runs.add(thisrun);
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
 // cout << "new nRuns = " << newnRuns << endl;
}







void PhasePlane::startRuns()
{
  
  if (runs.size() != Simulation::getInstance()->entities.size())
  {
    LOG("Can't start runs as Nentities in Simulation and Phase Plane differ. Exit.");
  }
  
  // loop over runs
  int count = -1;
  for (auto & run : runs)
  {
    count++;
   // set entity concentrations to their value in Phase Plane window
    //ControllableContainer * cc = run->getControllableContainerByName("run" + String(to_string(count)));
    juce::Array<juce::WeakReference<Parameter>> allp = run->getAllParameters();
    cout << allp.size() << endl;

    // loop over parameters contained in this run
    // and pass the initial concentrations to actual SimEntities
    for (auto & p : allp)
    {
      if (p->type == Controllable::Type::POINT3D)
      {
        //Point3DParameter pp = (Point3DParameter) p;
        //dynamic_cast<typePoint3DParameter*>(p);
        
        cout << "\tis point 3D" << endl;
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

        Simulation::getInstance()->getSimEntityForName(name1)->startConcent = x.operator float();
        Simulation::getInstance()->getSimEntityForName(name2)->startConcent = y.operator float();
        Simulation::getInstance()->getSimEntityForName(name3)->startConcent = z.operator float();
        
        //cout << "is array ? --> " << p->value.isArray() << endl;
        //var v = arr[0];
        //cout << "is Float ? --> " << v.isDouble() << endl;
        //float f = v.float();

        //cout << pname << ". array size = " << arr.size() << "  " << v.operator float() << endl;
        //cout << name1 << endl;
        //cout << name2 << endl;
        //cout << name3 << endl;
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

        Simulation::getInstance()->getSimEntityForName(name1)->startConcent = x.operator float();
        Simulation::getInstance()->getSimEntityForName(name2)->startConcent = y.operator float();
      }
      else if (p->type == Controllable::Type::FLOAT)
      {
        //cout << "\tis float" << endl;
        String name = p->niceName;
        //cout << "name : " << name << endl;
        //SimEntity * temp = Simulation::getInstance()->getSimEntityForName(name);
        Simulation::getInstance()->getSimEntityForName(name)->startConcent = p->floatValue();
        //cout << "got entity " << temp->name << endl;
      }
    } // end loop over parameter in run
    
    // at this stage SimEntities should have their correct init concent value
    // I can run simulation
    Settings::getInstance()->printHistoryToFile->setValue(true);
    Simulation::getInstance()->kRun = count;
    Simulation::getInstance()->start();
    
    // NB : above that works. Only the concentration dynamics file is "écrasé". Add an option to have it open and completed.
    
  } // end loop over runs
  
} // end startRuns()
