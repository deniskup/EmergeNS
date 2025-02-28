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
  userCanAddControllables = false;
  isRemovableByUser = true;
  updateEntitiesFromSimu();
}

Run::Run(String _name) : BaseItem(_name)
{
  //userCanRemove = true;
  //userCanAddControllables = false;
  //askConfirmationBeforeRemove = false;
  //isSavable = true;
  userCanAddControllables = false;
  isRemovableByUser = true;
  updateEntitiesFromSimu();
}


Run::Run(var data) : BaseItem()
{
  
  userCanAddControllables = false;
  isRemovableByUser = true;
  updateEntitiesFromSimu();
    
  // retrieve run name
  if (data.getDynamicObject()->hasProperty("niceName"))
    niceName = data.getDynamicObject()->getProperty("niceName");
    
  auto parameters = data.getProperty("parameters", juce::var());
  
  // loop over remaining parameters
  for (auto & p : *parameters.getArray())
  {
    String s = "";
    //cout << "has property name ? --> " << p.getDynamicObject()->hasProperty("name") << endl;
    if (p.getDynamicObject()->hasProperty("name"))
    {
      s = p.getDynamicObject()->getProperty("name").operator String();
      //cout << "it is ? --> " << s << endl;
    }
    
    auto value = p.getDynamicObject()->getProperty("value");
    if (value.isArray())
    {
      Array<var> arr = *value.getArray();
      if (arr.size()==3)
      {
        Point3DParameter * newp3d = addPoint3DParameter(s, "");
        float x = arr[0].operator float();
        float y = arr[1].operator float();
        float z = arr[2].operator float();
        //cout << x << " ; " << y << " ; " << z << endl;
        newp3d->setVector(x, y, z);
        p3d.add(newp3d);
      }
      else if (arr.size()==2)
      {
        p2d = addPoint2DParameter(s, "");
        p2d->setPoint(arr[0], arr[1]);
      }
    }
    else if (value.isDouble())
    {
      fp = addFloatParameter(s, "", value.operator double());
    }
    else
    {
      LOGWARNING(" Unknown type in run parameters");
    }
  } // end parameters loop
  
}






void Run::updateEntitiesFromSimu() // should rename importSimuEntitiesToRuns
{

  p3d.clear();
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
    float c1 = Simulation::getInstance()->entities[e1]->startConcent;
    float c2 = Simulation::getInstance()->entities[e2]->startConcent;
    float c3 = Simulation::getInstance()->entities[e3]->startConcent;
    //p3p.addPoint3DParameter(name, "Initial concentrations");
    Point3DParameter * localp3d = addPoint3DParameter(name, "Initial concentrations");
    localp3d->setVector(c1, c2, c3);
    p3d.add(localp3d);
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


void Run::controllableRemoved(Controllable* c)
{
  cout << "Run:: delete a controllable ! " << endl;
  //renameRuns();
}


void Run::clearItem()
{
  cout << "RUN::clearing item" << endl;
  BaseItem::clearItem();
}
/*
void Run::itemRemoved(Run*)
{
  cout << "this one ?" << endl;
}
*/



var Run::getJSONData()
{
  //return ControllableContainer::getJSONData();
  // add saved material specific to daughter class
  var data = new DynamicObject();
  data.getDynamicObject()->setProperty("niceName", niceName);
  
  
  // points 3D
  var vparameters;
  for (auto & p : p3d)
  {
    var v = new DynamicObject();
    v.getDynamicObject()->setProperty("name", p->niceName);
    v.getDynamicObject()->setProperty("value", p->getValue());
    vparameters.append(v);
  }
  // points 2D
  if (p2d != nullptr)
  {
    var vp2d = new DynamicObject();
    vp2d.getDynamicObject()->setProperty("name", p2d->niceName);
    vp2d.getDynamicObject()->setProperty("value", p2d->getValue());
    vparameters.append(vp2d);
  }
  // point
  if (fp != nullptr)
  {
    var vfp = new DynamicObject();
    vfp.getDynamicObject()->setProperty("name", fp->niceName);
    vfp.getDynamicObject()->setProperty("value", fp->getValue());
    vparameters.append(vfp);
  }
  // gather into parent parameter var
  data.getDynamicObject()->setProperty("parameters", vparameters);
  
  return data;
}



void Run::loadJSONData(var data, bool createIfNotThere)
{
  cout << "HEEEEEEEEEEERRRRRRRE" << endl;
  
  // retrieve run name
  if (data.getDynamicObject()->hasProperty("niceName"))
    niceName = data.getDynamicObject()->getProperty("niceName");
    
  auto parameters = data.getProperty("parameters", juce::var());
  
  // loop over remaining parameters
  for (auto & p : *parameters.getArray())
  {
    String s = "";
    cout << "has property name ? --> " << p.getDynamicObject()->hasProperty("name") << endl;
    if (p.getDynamicObject()->hasProperty("name"))
    {
      s = p.getDynamicObject()->getProperty("name").operator String();
      cout << "it is ? --> " << s << endl;
    }
    
    auto value = p.getDynamicObject()->getProperty("value");
    if (value.isArray())
    {
      Array<var> arr = *value.getArray();
      if (arr.size()==3)
      {
        Point3DParameter * newp3d = addPoint3DParameter(s, "");
        float x = arr[0].operator float();
        float y = arr[1].operator float();
        float z = arr[2].operator float();
        cout << x << " ; " << y << " ; " << z << endl;
        newp3d->setVector(x, y, z);
        p3d.add(newp3d);
      }
      else if (arr.size()==2)
      {
        p2d = addPoint2DParameter(s, "");
        p2d->setPoint(arr[0], arr[1]);
      }
    }
    else if (value.isDouble())
    {
      fp = addFloatParameter(s, "", value.operator double());
    }
    else
    {
      LOGWARNING(" Unknown type in run parameters");
    }
  } // end parameters loop
}


void Run::afterLoadJSONDataInternal()
{
  cout << "Run::afterLoadJSONDataInternal()" << endl;
}


// ******************************************************* //
/*


juce_ImplementSingleton(RunManager);


RunManager::RunManager() : BaseManager("Runs")
{
}

RunManager::~RunManager()
{
}

void RunManager::addItemInternal(Run * r, var params)
{
  cout << "RunManager::addItemInternal" << endl;
}
*/

// ******************************************************* //


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
  
  // path to software
  pathToEmergens = addStringParameter("absolute path to EmergeNS", "absolute path to folder EmergeNS", "/path/to/EmergeNS");
  
  // entites defining the 2D plane in which to draw
  xAxis = addTargetParameter("x axis", "x axis", EntityManager::getInstance());
  xAxis->targetType = TargetParameter::CONTAINER;
  //xAxis->maxDefaultSearchLevel = 0;
  //xAxis->setRootContainer(EntityManager::getInstance());

  yAxis = addTargetParameter("y axis", "y axis", EntityManager::getInstance());
  yAxis->targetType = TargetParameter::CONTAINER;
  

  // number of runs
  nRuns = addIntParameter("Number of runs", "Number of runs", 0, 0, 20);
  
 
   
  /*
  //for (unsigned int i=0; i<nRuns->intValue(); i++)
  for (unsigned int i=0; i<0; i++)
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
    thisrun->addEntitiesToRun();
    addChildControllableContainer(thisrun);
    //thisrun->fp = addFloatParameter("fp", "", 1.5);
    //addChildControllableContainer(thisrun->get());
    runs.add(thisrun);

    
  }
  */
  
}





PhasePlane::~PhasePlane()
{
}



/*
void PhasePlane::addEntity(Entity* e)
{
  //FloatParameter* fp = runs->addFloatParameter("Entity " + String(runs->controllables.size() + 1), "Entity " + String(runs->controllables.size() + 1), 0., 0., 100.);
  //if (e != nullptr) fp->setValueFromTarget(e, false);
  //fp->saveValueOnly = false;
  //fp->isRemovableByUser = true;
}
*/

void PhasePlane::updateEntitiesFromSimu()
{
  for (auto & r : runs)
  {
    r->updateEntitiesFromSimu();
  }
} // end method updateEntitiesFromSimu


/*
void PhasePlane::updateEntitiesInRuns()
{
  for (int i=0; i<runs.size();  i++)
  {
    //r.getControllableContainer()
    runs[i]->clear();
    addEntitiesToRun(*runs[i]);
  }
}
*/

void PhasePlane::onContainerParameterChanged(Parameter *p)
{
  //ControllableContainer::onContainerParameterChanged(p);
  
  if (p == nRuns)
  {
    if (nRuns->intValue()>runs.size()) // must add containers
    {
      for (int k=runs.size(); k<nRuns->intValue(); k++)
      {
        // with new version
        String name = "run " + String(to_string(k));
        Run * thisrun = new Run(name);
        addChildControllableContainer(thisrun);
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
    drawRuns();
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



void PhasePlane::drawRuns()
{
  
  // test that python3 is installed
  String testcommmand = "python3 " + pathToEmergens->stringValue() + "/Source/scripts/test.py > testpython3.txt";
  system(testcommmand.toUTF8());
  ifstream iftest;
  iftest.open("testpython3.txt");
  string testout;
  getline(iftest, testout);
  if (!(testout == "Hello EmergeNS"))
  {
    LOG("Check python3 is installed and check path to EmergeNS in Phase Plane window. Exit.");
    LOG("Current path : '" + pathToEmergens->stringValue() + "'");
    return;
  }
  system("rm testpython3.txt"); // remove test file from user's system
  
  // test presence of file drawTrajectories.py in EmergeNS
  String drawfilename = pathToEmergens->stringValue() + "/Source/scripts/drawPhasePlane.py";
  ifstream ifPP;
  //ifPP.open(drawfilename.toUTF8(), ifstream::in);
  ifPP.open("/Users/thomas_kosc/Modeles/EmergeNS/Source/scripts/drawPhasePlane.py");
  if (!ifPP.is_open())
  {
    LOG("Please check that path to script drawPhasePlane.py is correct. Exit.");
    LOG("Current path : '" + pathToEmergens->stringValue() + "/Source/scripts/drawPhasePlane.py" + "'");
    return;
  }
  else
  {
    ifPP.close();
  }
  
  // test presence of file concentrationDynamics.py in current directory
  String concfilename = "./concentrationDynamics.csv";
  ifstream ifconc;
  ifconc.open(concfilename.toUTF8());
  if (!ifconc.is_open())
  {
    LOG("No file concentrationDynamics.csv in current directory. Please run simulation before . Exit.");
    return;
  }
  else
  {
    ifconc.close();
  }
  
  // Prepare command to execute python file
  // # python3 drawPhasePlane.py --file ./concentrationDynamics_model4.csv -x '[A2]' -y '[B2]' --nruns 5 --sst ./steadyStates.csv
  String drawCommand = "python3 " + pathToEmergens->stringValue() + "/Source/scripts/drawPhasePlane.py "
  + "--file concentrationDynamics.csv";
  
  // set axis options
  if (xAxis->getTargetContainerAs<Entity>()==nullptr)
  {
    LOG("Please chose an entity as x Axis. Exit.");
    return;
  }
  if (yAxis->getTargetContainerAs<Entity>()==nullptr)
  {
    LOG("Please chose an entity as y Axis. Exit.");
    return;
  }
  drawCommand += " -x '[" + xAxis->getTargetContainerAs<Entity>()->niceName + "]'";
  drawCommand += " -y '[" + yAxis->getTargetContainerAs<Entity>()->niceName + "]'";
  
  // indicate number of runs
  //drawCommand += " --nruns " + String(to_string(runs.size()));
  drawCommand += " --nruns 2";
  
  // check that steady states have been calculated already
  int nsst = Simulation::getInstance()->steadyStatesList->stableStates.size();
  cout << "N stables states = " << nsst << endl;
  if (nsst==0)
  {
    LOG("Please calculate steady states before drawing. Exit.");
    return;
  }
  
  // print steady states to steadyState.csv, needed by python script
  ofstream ofSST;
  ofSST.open("./steadyStates.csv", ofstream::out);
  // first : only print entity names
  int c = -1;
  int nent = Simulation::getInstance()->entities.size();
  for (auto & state : Simulation::getInstance()->steadyStatesList->stableStates[0].state)
  {
    c++;
    string comma = ( (c==nent-1) ? "\n" : "," );
    ofSST << "[" << state.first->name << "]" << comma;
  }
  // add concentrations at seatdy states
  for (SteadyState & steadystate : Simulation::getInstance()->steadyStatesList->stableStates)
  {
    c = -1;
    cout << "### sst ###" << endl;
    for (auto & p : steadystate.state)
    {
      cout << "\t" << p.second << endl;
      c++;
      string comma = ( (c==nent-1) ? "\n" : "," );
      ofSST << p.second << comma;
    }
    //ofSST << "[" << sst.state.first->name << "]";
  }
  ofSST.close();
  
  // add steady state file to shell command
  drawCommand += " --sst ./steadyStates.csv";
  
  // sanity check
  cout << drawCommand << endl;
  
  // execute python script
  system(drawCommand.toUTF8());
  
  
  
} // end PhasePlane::drawRuns()





void PhasePlane::loadJSONData(var data, bool createIfNotThere)
{
  /*
  // ugly solution to get rid of ghost runs initiated
  while (runs.size()>0)
  {
    int krm = runs.size()-1;
    removeChildControllableContainer(runs[krm]);
    runs.removeLast(1);
  }
*/
  

    // load runs
  if (!data.getDynamicObject()->hasProperty("runs"))
  {
    LOGWARNING("couldn't retrieve any run from json file");
    return;
  }
  
  auto arrayruns = data.getProperty("runs", juce::var());
  // retrieve runs
 // cout << "is array ? --> " << data.getProperty("runs", juce::var()).isArray() << endl;
  
  if (!data.getProperty("runs", juce::var()).isArray())
  {
    LOGWARNING(" Runs not stored as array in json file, will not init them");
    return;
  }
  
  
  // loop over stored runs
  for (auto & arun : *arrayruns.getArray())
  {
    if (!arun.getDynamicObject()->hasProperty("parameters"))
    {
      LOGWARNING(" No parameters in run.");
      return;
    }
    
    Run * newrun = new Run(arun);
    addChildControllableContainer(newrun);
    //cout << "adding child container with name " << newrun->niceName << endl;
    runs.add(newrun);
    
  }
  
  if (data.getDynamicObject()->hasProperty("nRuns"))
    nRuns->setValue(data.getDynamicObject()->getProperty("nRuns"));
  
  if (data.getDynamicObject()->hasProperty("pathToEmergens"))
    pathToEmergens->setValue(data.getDynamicObject()->getProperty("pathToEmergens"));
  
  if (data.getDynamicObject()->hasProperty("xAxis"))
    xAxis->setValue(data.getDynamicObject()->getProperty("xAxis"));
  
  if (data.getDynamicObject()->hasProperty("yAxis"))
    yAxis->setValue(data.getDynamicObject()->getProperty("yAxis"));
  
  
}





var PhasePlane::getJSONData()
{
  // add saved material specific to daughter class
  var data = new DynamicObject();
  data.getDynamicObject()->setProperty("pathToEmergens", pathToEmergens->stringValue());
  data.getDynamicObject()->setProperty("xAxis", xAxis->getValue());
  data.getDynamicObject()->setProperty("yAxis", yAxis->getValue());
  data.getDynamicObject()->setProperty("nRuns", nRuns->intValue());

  var vruns;
  for (auto& r : runs)
  {
    var v = r->getJSONData();
    vruns.append(v);
  }
  data.getDynamicObject()->setProperty("runs", vruns);

  
  return data;
  
}


