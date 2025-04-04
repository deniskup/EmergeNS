// 
//  PhasePlane.h
//  EmergeNS - App
//
//  Created by Thomas Kosc on 10/02/2025.
//

/*
TODO list
- I shouldn't have  Simulation.h included in this header. Circular inclusion pattern.
- Steady States do not seem to be saved in json file.
- nouveau thread pour script python
*/

#pragma once

#include "JuceHeader.h"
#include "Entity.h"
#include "Simulation.h"
#include "Settings.h"

//class Simulation;
using namespace juce;

//class Simulation;


//class Run : public BaseItem
class Run : public ControllableContainer
{
  public:
  Run();
  Run(String _name);
  Run(var data);
  Run(String, Array<String>, Array<float>); // entity names, entity concentrations
  Run(OwnedArray<SimEntity*>, String _name);
  virtual ~Run(){};
  
  //String name = "";
  Array<Point3DParameter*> p3d;
  Point2DParameter * p2d = nullptr;
  FloatParameter * fp = nullptr;
  
    
  void addEntitiesToRun(Array<String>, Array<float>);
  
  void clearEntities();
  
  void importConcentrationsFromSimu();
  
  void controllableRemoved(Controllable* c) override;
  //void clearItem() override;


  
  var getJSONData(bool includeNonOverriden = false) override; // à coder, voir  var toJSONData() de Simulation.h
  //var toJSONData(); // à coder, voir  var toJSONData() de Simulation.h
  
  void loadJSONData(var data, bool createIfNotThere = false) override; //
  
  void afterLoadJSONDataInternal() override;
  
  //void itemRemoved(typename T*) override; 

};

/*
class RunManager :
  public BaseManager<Run>
{
public:
  juce_DeclareSingleton(RunManager,true);
  RunManager();
  ~RunManager();

  //void autoRename();
  //void inferAllReacs();
  
  void addItemInternal(Run * r, var params) override;

  //Run * getRunFromName(const String &searchName);

};
*/



class PhasePlane : public ControllableContainer, public Thread
{
public:
    juce_DeclareSingleton(PhasePlane, true);
    PhasePlane();
    PhasePlane(var data); // import from JSON

    ~PhasePlane();
  
  Trigger * start;
  Trigger * draw;
  //Trigger * startDraw;
  
  String pathToEmergens;
  
  TargetParameter * xAxis;
  TargetParameter * yAxis;
  
  Trigger * importCSV;
  StringParameter * pathToCSV;

  Trigger * syncWithSimu;


  IntParameter * nRuns;
  Array<Run*> runs;
  
  bool isRemoving = false;
  
  //void addEntity(Entity* e);
  //void addEntitiesToRun(ControllableContainer &);
  void updateEntitiesFromSimu();
  void updateRunsNames();
  
  void onContainerParameterChanged(Parameter* p) override;
  void onContainerTriggerTriggered(Trigger* t) override;
  void onChildContainerRemoved(ControllableContainer*) override;
  
  void itemRemoved(ControllableContainer*);

  void clearAllRuns();
  void addRun(Run *);
  
  void importRunsFromCSVFile();
  
  void startRuns();
  void drawRuns();
  void run() override; // thread function

  
  
  void loadJSONData(var data, bool createIfNotThere = false) override;
  var getJSONData(bool includeNonOverriden = true) override;
  
 
  





  
    //void onContainerParameterChanged(Parameter *p) override;

  class PhasePlaneListener
  {
  public:
  virtual ~PhasePlaneListener() {}
  virtual void updatePhasePlaneUI(PhasePlane *){};
  };
  
  
  ListenerList<PhasePlaneListener> listeners;
  void addPhasePlaneListener(PhasePlaneListener *newListener) { listeners.add(newListener); }
  void removePhasePlaneListener(PhasePlaneListener *listener) { listeners.remove(listener); }

};
