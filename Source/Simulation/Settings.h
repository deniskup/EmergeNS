
#pragma once

#include "JuceHeader.h"
// #include <unordered_map>

class Settings : public ControllableContainer
{
public:
    juce_DeclareSingleton(Settings, true);
    Settings();
    ~Settings();

    StringParameter *pathToKissat; 

    IntParameter *maxDiameterPACs;
    IntParameter *maxDoubleReacPACs;


    //void onContainerParameterChanged(Parameter *p) override;

  //   class SettingsListener
  // {
  // public:
  //   virtual ~SettingsListener() {}
  //   virtual void updateSettingsUI(Settings *){};
  // };

  // ListenerList<SettingsListener> listeners;
  // void addSettingsListener(SettingsListener *newListener) { listeners.add(newListener); }
  // void removeSettingsListener(SettingsListener *listener) { listeners.remove(listener); }
};
