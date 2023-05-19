#include "Settings.h"

juce_ImplementSingleton(Settings);

Settings::Settings() : ControllableContainer("Settings")
{

    pathToKissat = addStringParameter("Path to kissat", "Path to kissat solver", "~/Software/kissat/build/kissat");

    maxDiameterPACs = addIntParameter("Max diameter PACs", "Maximal diameter in PAC searching", 20, 1);

    maxPACperDiameter = addIntParameter("Max PACs per diameter", "Timeout for number of PACs of some diameter", 300, 1);

    maxDoubleReacPACs = addIntParameter("Max double reactions PACs", "Maximal number of double reactions in PAC searching", 2, 0);

    printPACsToFile = addBoolParameter("Print PACs to file", "Print PACs to file PAC_list.txt", false);

}

Settings::~Settings()
{
}

