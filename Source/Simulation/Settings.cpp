#include "Settings.h"


juce_ImplementSingleton(Settings);

Settings::Settings() : ControllableContainer("Settings")
{


    maxDiameterPACs = addIntParameter("Max size", "Maximal size in PAC searching", 20, 1);

    maxPACperDiameter = addIntParameter("Max #PACs per size", "Timeout for number of PACs of some size", 300, 1);

    CACSetMax = addIntParameter("Max Set CACs", "Maximal simultaneous CACs to test", 6, 1);

    CACRobustness = addFloatParameter("CAC Robustness", "Threshold for CAC witness", .0001, .0);

    CacAccelUse = addBoolParameter("CAC Acceleration", "Use acceleration threshold for CAC search", false);

    CACAccelThresh = addFloatParameter("CAC Accel. Thresh.", "Acceleration threshold for CAC search", .0);

    //maxDoubleReacPACs = addIntParameter("(SAT) Max doubleReac", "Maximal number of double reactions in PAC searching", 2, 0);

    printPACsToFile = addBoolParameter("Print PACs to file", "Print PACs to file PAC_list.txt", false);

    printHistoryToFile = addBoolParameter("Print History to file", "Print concentrations and RACS to history.csv", false);

    nonMinimalPACs = addBoolParameter("Non minimal PACs", "Look for non minimal PACs", false);

    pathToz3 = addStringParameter("Path to z3", "Path to z3 solver", "/usr/local/bin/z3");

    pathToMSolve = addStringParameter("Path to msolve", "Path to msolve", "/usr/local/bin/msolve");

    z3timeout = addIntParameter("z3 timeout", "Timeout for z3 in ms", 2000, 0);

    autoLoadLists = addBoolParameter("Auto load lists", "Auto load manual lists on generation", true);

    CACRobustness->setAttributeInternal("stringDecimals", CACROB_PRECISION);

    csvFile = addStringParameter("CSV Reactions file", "Path to CSV file to import a list of reactions", "");


}

Settings::~Settings()
{
}

