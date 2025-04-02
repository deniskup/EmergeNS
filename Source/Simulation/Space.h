
#pragma once

#include "JuceHeader.h"
#define CACROB_PRECISION 5

using namespace juce;

class Space : public ControllableContainer
{
public:
    juce_DeclareSingleton(Space, true);
    Space();
    ~Space();

   
    IntParameter * tilingSize; //
    
  
    void onContainerParameterChanged(Parameter *p) override;
    
    void afterLoadJSONDataInternal() override;


  //   class SettingsListener
  // {
  // public:
  //   virtual ~SettingsListener() {
  //   virtual void updateSettingsUI(Settings *){};
  // };

  // ListenerList<SettingsListener> listeners;
  // void addSettingsListener(SettingsListener *newListener) { listeners.add(newListener); }
  // void removeSettingsListener(SettingsListener *listener) { listeners.remove(listener); }
};
