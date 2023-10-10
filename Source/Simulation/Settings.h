
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

    IntParameter *maxDiameterPACs; //diameter to stop
    IntParameter *maxPACperDiameter; //timeout for number of PACs of some diameter
    IntParameter *maxDoubleReacPACs; //maximal number of double reactions to look for

    BoolParameter *nonMinimalPACs; //look for non minimal PACs

    BoolParameter *printPACsToFile; //print PACs to file

    BoolParameter *autoLoadLists;

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
