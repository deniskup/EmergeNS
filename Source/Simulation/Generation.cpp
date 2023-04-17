#include "Generation.h"

juce_ImplementSingleton(Generation);

Generation::Generation() : ControllableContainer("Generation")
{

    primEntities = addIntRangeParameter("Primary entities", "Number of primary entities");
    primEntities->x=3;
    primEntities->y=10;

    numLevels = addIntRangeParameter("Levels", "Number of levels");
    numLevels->x=10;
    numLevels->y=20;

    growthEntitiesPerLevel = addEnumParameter("Growth entities/level", "How the number of entities increase per level. Constant gives n+range[-u,u], Polynomial is a*level^b+range[-u,u], Proportion is a proportion 'a' of the total number of entities (1 for all)");
    growthEntitiesPerLevel->addOption("Constant", CONSTANT)->addOption("Polynomial", POLYNOMIAL)->addOption("Proportion", PROPORTION);
    // growthEntitiesPerLevel->hideInEditor = true;

    entPerLevNum = addIntRangeParameter("Entities/level", "Base number of entities per level");
    entPerLevNum->x = 3;
    entPerLevNum->y = 6;

    entPerLevA = addFloatParameter("Coef a #entities", "Maximal creation rate of primary entities", .1, 0.);
    entPerLevA->hideInEditor=true;
    
    entPerLevB = addFloatParameter("Exponent level^b #entities", "Exponent of polynomial growth", 2., 0.);
    entPerLevB->hideInEditor=true;
    
    entPerLevUncert = addIntParameter("Plus minus u", "Uncertainty on entity per level: +range[-u,u]", 5, 0);
    entPerLevUncert->hideInEditor=true; 
    //old
   // maxReactionsPerEntity = addIntParameter("Max reactions per entity", "Maximal number of reactions forming an entity", 3, 1, 100);

    reactionsPerEntity = addIntRangeParameter("Reactions per entity", "Min and max number of reactions forming an entity");
    reactionsPerEntity->x = 1;
    reactionsPerEntity->y = 3;

    concentRange = addPoint2DParameter("Init. concentration range", "Min and Max initial concentrations for primary entities");
    concentRange->x = 0.f;
    concentRange->y = 1.f;
    maxCreationRate = addFloatParameter("Max creation rate", "Maximal creation rate of primary entities", .5, 0.);
    maxDestructionRate = addFloatParameter("Max destruction rate", "Maximal destruction rate of entities", .5, 0.);
    energyPerLevel = addFloatParameter("Energy per level", "Base energy of composite entities is coef*level", .5);
    energyUncertainty = addFloatParameter("Energy uncertainty", "Energy=Base energy +-uncertainty", .5, 0.);
    maxEnergyBarrier = addFloatParameter("Max energy barrier", "Max energy barrier of reactions", .1, 0.);

    avgNumShow = addIntParameter("Max num of curves", "Expected number of entities to follow", 10, 1, 100);
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
            entPerLevUncert->hideInEditor=true;
            break;
        case POLYNOMIAL:
            entPerLevNum->hideInEditor = true;
            entPerLevA->hideInEditor = false;
            entPerLevB->hideInEditor = false;
            entPerLevUncert->hideInEditor=false;
            break;
        case PROPORTION:
            entPerLevNum->hideInEditor = true;
            entPerLevA->hideInEditor = false;
            entPerLevB->hideInEditor = true;
            entPerLevUncert->hideInEditor=false;
            break;
        default:
            break;
        }
        listeners.call(&GenerationListener::updateGrowth, this);
        //a faire : send message to listener GenerationUI to update
    }
}