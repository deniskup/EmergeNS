#include "Settings.h"

juce_ImplementSingleton(Settings);

Settings::Settings() : ControllableContainer("Settings")
{


    maxDiameterPACs = addIntParameter("Max size", "Maximal size in PAC searching", 20, 1);

    maxPACperDiameter = addIntParameter("Max #PACs per size", "Timeout for number of PACs of some size", 300, 1);

    maxDoubleReacPACs = addIntParameter("(SAT) Max doubleReac", "Maximal number of double reactions in PAC searching", 2, 0);

    printPACsToFile = addBoolParameter("Print PACs to file", "Print PACs to file PAC_list.txt", false);

    nonMinimalPACs = addBoolParameter("Non minimal PACs", "Look for non minimal PACs", false);

    pathToKissat = addStringParameter("Path to kissat", "Path to kissat solver", "~/Software/kissat/build/kissat");

    autoLoadLists = addBoolParameter("Auto load lists", "Auto load manual lists on generation", true);

}

Settings::~Settings()
{
}

