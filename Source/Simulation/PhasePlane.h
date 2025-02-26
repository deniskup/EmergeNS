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
- add posiibility to scroll within this window.
- sync nRuns with runs actually manually removed, and rename the runs starting from 0 when one is actually removed.
- I shouldn't have  Simulation.h included in this header. Circular inclusion pattern.
- fix save and import data as JSON.
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


class Run : public BaseItem
{
  public:
  Run();
  Run(String _name);
  Run(OwnedArray<SimEntity*>, String _name);
  virtual ~Run(){};
  
    String name = "";
    Array<Point3DParameter*> p3p;
    Point2DParameter * p2d;
    FloatParameter * fp;
  
  //void addEtitiesToRun(OwnedArray<SimEntity*>);
  void addEtitiesToRun();
};


class RunManager :
  public BaseManager<Run>
{
public:
  juce_DeclareSingleton(RunManager,true);
  RunManager();
  ~RunManager();

  //void autoRename();
  //void inferAllReacs();

  Run * getRunFromName(const String &searchName);

};




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

  IntParameter * nRuns;
  //Array<ControllableContainer*> runs;
  //vector<ControllableContainer*> runs(20);
  //ControllableContainer * arun;
  //ControllableContainer * test;
  Array<Run*> runs;
  
  void addEntity(Entity* e);
  void addEntitiesToRun(ControllableContainer &);
  void updateEntitiesInRuns();
  
  void onContainerParameterChanged(Parameter* p) override;
  void onContainerTriggerTriggered(Trigger* t) override;
  
  void controllableAdded(Controllable *) override;
  void controllableRemoved(Controllable *) override;
  
  void startRuns();
  void drawRuns();

  
  //void importJSONData(var data);
  
  //void afterLoadJSONDataInternal() override;



  
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
