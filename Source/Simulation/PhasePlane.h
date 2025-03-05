//
//  PhasePlane.h
//  EmergeNS - App
//
//  Created by Thomas Kosc on 10/02/2025.
//

/*
TODO list
- synchronize manual addition of entities with Phase Plane entity list
- manually position the trigger buttons instead of using three lines. See PhasePlaneUI for that.
- I shouldn't have  Simulation.h included in this header. Circular inclusion pattern.
- Steady States do not seem to be saved in json file.
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
  
  String name = "";
  Array<Point3DParameter*> p3d;
  Point2DParameter * p2d = nullptr;
  FloatParameter * fp = nullptr;
  
  //void controllableAdded(Controllable *) override; // à coder
    
  void addEntitiesToRun(Array<String>, Array<float>);
  
  void importConcentrationsFromSimu();
  
  void controllableRemoved(Controllable* c) override;
  //void clearItem() override;


  
  var getJSONData() override; // à coder, voir  var toJSONData() de Simulation.h
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



class PhasePlane : public ControllableContainer
//class PhasePlane : public BaseItem
{
public:
    juce_DeclareSingleton(PhasePlane, true);
    PhasePlane();
    PhasePlane(var data); // import from JSON

    ~PhasePlane();
  
  Trigger * start;
  Trigger * draw;
  Trigger * startDraw;
  
  StringParameter * pathToEmergens;
  
  TargetParameter * xAxis;
  TargetParameter * yAxis;
  
  Trigger * importCSV;
  StringParameter * pathToCSV;



  IntParameter * nRuns;
  Array<Run*> runs;
  
  //void addEntity(Entity* e);
  //void addEntitiesToRun(ControllableContainer &);
  void updateEntitiesFromSimu();
  void updateRunsNames();
  
  void onContainerParameterChanged(Parameter* p) override;
  void onContainerTriggerTriggered(Trigger* t) override;
  void controllableAdded(Controllable *) override;
  void onRemoveChildControllableContainer() override;

  void clearAllRuns();
  void addRun(Run *);
  
  void importRunsFromCSVFile();
  
  void startRuns();
  void drawRuns();

  
  
  void loadJSONData(var data, bool createIfNotThere = false) override; // à coder, voir void importJSONData(var data) de Simulation.h
  var getJSONData() override; // à coder, voir  var toJSONData() de Simulation.h
  
 
  





  
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
