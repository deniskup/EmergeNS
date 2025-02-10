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


    //void onContainerParameterChanged(Parameter *p) override;

  //  class GenerationListener
 // {
 // public:
 //   virtual ~GenerationListener() {}
 //   virtual void updateGenUI(Generation *){};
 // };

 // ListenerList<GenerationListener> listeners;
 // void addGenerationListener(GenerationListener *newListener) { listeners.add(newListener); }
 // void removeGenerationListener(GenerationListener *listener) { listeners.remove(listener); }
};
