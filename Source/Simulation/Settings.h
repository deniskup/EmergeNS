
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
    
    IntParameter *minDiameterPACs; //
    IntParameter *maxDiameterPACs; //diameter to stop
    IntParameter *maxPACperDiameter; //timeout for number of PACs of some diameter

    StringParameter *PACmustContain; //some entity that PACs must contain

    BoolParameter *multiPACs; //look for multiPACs

    BoolParameter *primFood; //only primary can be food

    IntParameter *CACSetMax; //maximal number of PACs to look for
    //IntParameter *maxDoubleReacPACs; //maximal number of double reactions to look for

    FloatParameter *CACRobustness; //threshold for accepting CAC witness
    BoolParameter *CacAccelUse; //acceleration threshold for CAC search
    FloatParameter *CACAccelThresh; //acceleration threshold for CAC search
    FloatParameter *CACConcBound; //bound on the concentration for CAC witnesses, 0 or negative for no bound

    BoolParameter *nonMinimalPACs; //look for non minimal PACs


    BoolParameter *printPACsToFile; //print PACs to file

    BoolParameter *printSteadyStatesToFile; //print SteadyStates to file

    BoolParameter *printHistoryToFile; //print RACs to file

    BoolParameter * userListMode;



    StringParameter * csvFile; // if used, input excel file name
  
    FloatParameter * volume;
    FloatParameter * epsilonNoise;
    BoolParameter * fixedSeed;
    StringParameter * randomSeed;

    
    void onContainerParameterChanged(Parameter *p) override;
  
    void updateNoiseParameter(); // recalculate epsilon noise parameter from volume of the system
  
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
