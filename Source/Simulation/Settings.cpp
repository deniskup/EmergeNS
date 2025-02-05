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

    printHistoryToFile = addBoolParameter("Print History to file", "Print concentrations and RACS to history.csv", false);

    nonMinimalPACs = addBoolParameter("Non minimal PACs", "Look for non minimal PACs", false);

    pathToz3 = addStringParameter("Path to z3", "Path to z3 solver", "/usr/local/bin/z3");

    pathToMSolve = addStringParameter("Path to msolve", "Path to msolve", "/usr/local/bin/msolve");

    z3timeout = addIntParameter("z3 timeout", "Timeout for z3 in ms", 2000, 0);

    userListMode = addBoolParameter("User list mode", "Synchronize manual lists with simulation at all times", true);

    CACRobustness->setAttributeInternal("stringDecimals", CACROB_PRECISION);

    csvFile = addStringParameter("CSV Reactions file", "Path to CSV file to import a list of reactions", "");

    systemSize = addFloatParameter("LOG10 system size (m)", "LOG10 of the size L (expressed in meters) of the system used to calculate its volume L^3", -2.f, -7.f, 0.f);


}

Settings::~Settings()
{
}

