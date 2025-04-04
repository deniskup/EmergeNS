
#pragma once

#include "JuceHeader.h"
#define CACROB_PRECISION 5

using namespace juce;
using namespace std;

class Space : public ControllableContainer
{
public:
    juce_DeclareSingleton(Space, true);
    Space();
    ~Space();

   
    IntParameter * tilingSize; //
  
    int previousTiling;
    
  
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
