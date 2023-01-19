#include "Generation.h"

juce_ImplementSingleton(Generation);

    Generation::Generation() : ControllableContainer("Generation")
{

    
    entitiesPerLevel = addIntParameter("Entities per level", "Entities per Level", 5,1, 500);
    maxReactionsPerEntity = addIntParameter("Reactions per entity", "Maximal number of reactions forming an entity",3, 1, 100);
    numLevels = addIntParameter("Levels", "Number of levels",10, 1, 1000);
    concentRange = addPoint2DParameter("Init. concentration range", "Min and Max initial concentrations for primary entities");
    concentRange->x=0.f;
    concentRange->y=1.f;  
    maxCreationRate=addFloatParameter("Max creation rate", "Maximal creation rate of primary entities", .5,0.);
    maxDestructionRate=addFloatParameter("Max destruction rate", "Maximal destruction rate of entities", .5,0.);
    energyPerLevel=addFloatParameter("Energy per level", "Base energy of composite entities is -coef*level", .5,0.);
    energyUncertainty=addFloatParameter("Energy uncertainty", "Energy=Base energy +-uncertainty", .5,0.);
    maxEnergyBarrier=addFloatParameter("Max ernergy barrier", "Max energy barrier of reactions", .1,0.);

    avgNumShow = addIntParameter("Avg num of curves", "Expected number of entities to follow",10, 1, 100);
    //minG = addFloatParameter("Min G", "Current step in the simulation", 0, 0, maxSteps->intValue());
}

Generation::~Generation()
{
}