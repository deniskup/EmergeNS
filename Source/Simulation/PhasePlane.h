//
//  PhasePlane.h
//  EmergeNS - App
//
//  Created by Thomas Kosc on 10/02/2025.
//

/*
TODO list
- synchronize manual of addition of entities with Phase Plane entity list
- manually position the trigger buttons instead of using three lines. See PhasePlaneUI for that
- add posiibility to scroll within this window
- sync nRuns with runs actually manually removed
- I shouldn't have  Simulation.h included in this header
*/

#pragma once

#include "JuceHeader.h"
#include "Entity.h"
#include "Simulation.h"
#include "Settings.h"

// #include <unordered_map>
using namespace juce;

//class Simulation;


class PhasePlane : public ControllableContainer
//class PhasePlane : public BaseItem
{
public:
    juce_DeclareSingleton(PhasePlane, true);
    PhasePlane();
    ~PhasePlane();

  Trigger * start;
  Trigger * draw;
  Trigger * startDraw;
  
  TargetParameter * xAxis;
  TargetParameter * yAxis;

  IntParameter * nRuns;
  Array<ControllableContainer*> runs;
  
  
  void addEntity(Entity* e);
  void addEntitiesToRun(ControllableContainer &);
  void updateEntitiesInRuns();
  
  void onContainerParameterChanged(Parameter* p) override;
  void onContainerTriggerTriggered(Trigger* t) override;
  
  void controllableAdded(Controllable *) override;
  void controllableRemoved(Controllable *) override;
  
  void startRuns();


  
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
