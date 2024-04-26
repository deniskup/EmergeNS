
#pragma once

#include "JuceHeader.h"
// #include <unordered_map>
#define CACROB_PRECISION 5

using namespace juce;

class Settings : public ControllableContainer
{
public:
    juce_DeclareSingleton(Settings, true);
    Settings();
    ~Settings();

    StringParameter *pathToz3; 
    StringParameter *pathToMSolve; 

    IntParameter *z3timeout; //timeout for z3 in ms
    
    IntParameter *maxDiameterPACs; //diameter to stop
    IntParameter *maxPACperDiameter; //timeout for number of PACs of some diameter
    IntParameter *CACSetMax; //maximal number of PACs to look for
    //IntParameter *maxDoubleReacPACs; //maximal number of double reactions to look for

    FloatParameter *CACRobustness; //threshold for accepting CAC witness
    BoolParameter *CacAccelUse; //acceleration threshold for CAC search
    FloatParameter *CACAccelThresh; //acceleration threshold for CAC search


    BoolParameter *nonMinimalPACs; //look for non minimal PACs


    BoolParameter *printPACsToFile; //print PACs to file

    BoolParameter *autoLoadLists;

    StringParameter * csvFile; // if used, input excel file name

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
