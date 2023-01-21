#include "Generation.h"

juce_ImplementSingleton(Generation);

Generation::Generation() : ControllableContainer("Generation")
{

    numLevels = addIntParameter("Levels", "Number of levels", 10, 1, 1000);

    growthEntitiesPerLevel = addEnumParameter("Growth entities/level", "How the number of entities increase per level. Constant gives n+range[-u,u], Polynomial is a*level^b+range[-u,u], Exponential is a*b^level+range[-u,u]");
    growthEntitiesPerLevel->addOption("Constant", CONSTANT)->addOption("Polynomial", POLYNOMIAL)->addOption("Exponential", EXPONENTIAL);
    // growthEntitiesPerLevel->hideInEditor = true;

    entPerLevNum = addIntParameter("Num n #entities", "Base number of entities per level", 5, 0);
    entPerLevA = addFloatParameter("Coef a #entities", "Maximal creation rate of primary entities", 2., 0.);
    entPerLevA->hideInEditor=true;
    
    entPerLevB = addFloatParameter("Param b #entities", "Exponent or base of growth for poly/exp", 2., 0.);
    entPerLevB->hideInEditor=true;
    
    entPerLevUncert = addIntParameter("Plus minus u", "Uncertainty on entity per level: +range[-u,u]", 5, 0);

    maxReactionsPerEntity = addIntParameter("Reactions per entity", "Maximal number of reactions forming an entity", 3, 1, 100);

    concentRange = addPoint2DParameter("Init. concentration range", "Min and Max initial concentrations for primary entities");
    concentRange->x = 0.f;
    concentRange->y = 1.f;
    maxCreationRate = addFloatParameter("Max creation rate", "Maximal creation rate of primary entities", .5, 0.);
    maxDestructionRate = addFloatParameter("Max destruction rate", "Maximal destruction rate of entities", .5, 0.);
    energyPerLevel = addFloatParameter("Energy per level", "Base energy of composite entities is -coef*level", .5, 0.);
    energyUncertainty = addFloatParameter("Energy uncertainty", "Energy=Base energy +-uncertainty", .5, 0.);
    maxEnergyBarrier = addFloatParameter("Max ernergy barrier", "Max energy barrier of reactions", .1, 0.);

    avgNumShow = addIntParameter("Avg num of curves", "Expected number of entities to follow", 10, 1, 100);
    // minG = addFloatParameter("Min G", "Current step in the simulation", 0, 0, maxSteps->intValue());
}

Generation::~Generation()
{
}

void Generation::onContainerParameterChanged(Parameter *p)
{
    if (p == growthEntitiesPerLevel)
    {
        switch (growthEntitiesPerLevel->getValueDataAsEnum<GrowthMode>())
        {
        case CONSTANT:
            entPerLevNum->hideInEditor = false;
            entPerLevA->hideInEditor = true;
            entPerLevB->hideInEditor = true;
            DBG("Constant");
            break;
        case POLYNOMIAL:
        case EXPONENTIAL:
            entPerLevNum->hideInEditor = true;
            entPerLevA->hideInEditor = false;
            entPerLevB->hideInEditor = false;
            DBG("Not constant");
            break;
        default:
            break;
        }
        listeners.call(&GenerationListener::updateGrowth, this);
        //a faire : send message to listener GenerationUI to update
    }
}