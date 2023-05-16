#include "Settings.h"

juce_ImplementSingleton(Settings);

Settings::Settings() : ControllableContainer("Settings")
{

    pathToKissat = addStringParameter("Path to kissat", "Path to kissat solver", "~/Downloads/kissat/build/kissat");

    maxDiameterPACs = addIntParameter("Max diameter PACs", "Maximal diameter in PAC searching", 20, 1, 100);

    maxDoubleReacPACs = addIntParameter("Max double reactions PACs", "Maximal number of double reactions in PAC searching", 5, 0, 100);

}

Settings::~Settings()
{
}

