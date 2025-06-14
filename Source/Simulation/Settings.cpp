#include "Settings.h"


juce_ImplementSingleton(Settings);

Settings::Settings() : ControllableContainer("Settings")
{

    minDiameterPACs = addIntParameter("Min PAC size", "Minimal size in PAC searching", 1, 1);

    maxDiameterPACs = addIntParameter("Max PAC size", "Maximal size in PAC searching", 20, 1);

    maxPACperDiameter = addIntParameter("Max #PACs per size", "Timeout for number of PACs of some size", 300, 1);

    PACmustContain = addStringParameter("PAC must contain", "some entity that PACs must contain", "");

    multiPACs =  addBoolParameter("MultiPACs","Look for MultiPACs", false);

    primFood = addBoolParameter("Primary food", "Only primary can be food", false);

    CACSetMax = addIntParameter("Max Set CACs", "Maximal simultaneous CACs to test", 6, 1);

    CACRobustness = addFloatParameter("CAC Robustness", "Threshold for CAC witness", .0001, .0);

    CacAccelUse = addBoolParameter("CAC Acceleration", "Use acceleration threshold for CAC search", false);

    CACAccelThresh = addFloatParameter("CAC Accel. Thresh.", "Acceleration threshold for CAC search", .0);

    CACConcBound = addFloatParameter("CAC Conc. Bound", "Bound on the concentration for CAC witnesses, 0 or negative for no bound", .0);

    //maxDoubleReacPACs = addIntParameter("(SAT) Max doubleReac", "Maximal number of double reactions in PAC searching", 2, 0);

    printPACsToFile = addBoolParameter("Print PACs to file", "Print PACs to file PAC_list.txt", false);
  
    printSteadyStatesToFile = addBoolParameter("Print steady states to file", "Print steady states to file SteadyStates.txt", false);

    printHistoryToFile = addBoolParameter("Print History to file", "Print concentrations and RACS to history.csv", false);

    nonMinimalPACs = addBoolParameter("Non minimal PACs", "Look for non minimal PACs", false);

    pathToz3 = addStringParameter("Path to z3", "Path to z3 solver", "/usr/local/bin/z3");

    pathToMSolve = addStringParameter("Path to msolve", "Path to msolve", "/usr/local/bin/msolve");

    z3timeout = addIntParameter("z3 timeout", "Timeout for z3 in ms", 2000, 0);

    userListMode = addBoolParameter("User list mode", "Synchronize manual lists with simulation at all times", true);

    CACRobustness->setAttributeInternal("stringDecimals", CACROB_PRECISION);

    csvFile = addStringParameter("CSV Reactions file", "Path to CSV file to import a list of reactions", "");

    volume = addFloatParameter("LOG10 volume", "LOG10 of the volume of the system", 4.f, 0.f, 10.f);
    
    epsilonNoise = addFloatParameter("epsilon noise", "noise parameter of Langevin equation associated to current system's volume", 0.1f);
    epsilonNoise->setControllableFeedbackOnly(true);
    epsilonNoise->setAttributeInternal("stringDecimals", 7);
  
    updateNoiseParameter();
  
    fixedSeed = addBoolParameter("Fix seed of random generator", "Fix seed of random generator", false);
   
    randomSeed = addStringParameter("Seed of random generator", "Seed of random generator", "1234");
    randomSeed->setControllableFeedbackOnly(!fixedSeed->boolValue());

}

Settings::~Settings()
{
}

void Settings::onContainerParameterChanged(Parameter *p)
{
  if (p == volume)
  {
    updateNoiseParameter();
  }
  else if (p == fixedSeed)
  {
    randomSeed->setControllableFeedbackOnly(!fixedSeed->boolValue());
  }
}

void Settings::updateNoiseParameter()
{
  // calculate new value
  float logvol = volume->floatValue();
  float epsi = 1. / sqrt(pow(10., logvol));
  var vepsi(epsi);
  epsilonNoise->setValue(epsi);
  
  epsilonNoise->setControllableFeedbackOnly(true);
  epsilonNoise->setAttributeInternal("stringDecimals", 7);
}

void Settings::afterLoadJSONDataInternal()
{
  updateNoiseParameter();
}


