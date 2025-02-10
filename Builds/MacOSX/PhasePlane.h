//
//  PhasePlane.h
//  EmergeNS - App
//
//  Created by Thomas Kosc on 10/02/2025.
//

#pragma once

#include "JuceHeader.h"
// #include <unordered_map>
using namespace juce;

class PhasePlane : public ControllableContainer
{
public:
    juce_DeclareSingleton(PhasePlane, true);
    PhasePlane();
    ~PhasePlane();

   
  void init();
  
  void drawPhasePlaneTrajectories();


  FloatParameter * test;
  
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
