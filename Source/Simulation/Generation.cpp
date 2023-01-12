#include "Generation.h"

juce_ImplementSingleton(Generation);

    Generation::Generation() : ControllableContainer("Generation")
{

    
    entitiesPerLevel = addIntParameter("Entities per level", "Entities per Level", 5,1, 50);
    maxReactionsPerEntity = addIntParameter("Reactions per entity", "Maximal number of reactions forming an entity",3, 1, 10);
    numLevels = addIntParameter("Levels", "Number of levels",10, 1, 100);
    //minG = addFloatParameter("Min G", "Current step in the simulation", 0, 0, maxSteps->intValue());
}

Generation::~Generation()
{
}