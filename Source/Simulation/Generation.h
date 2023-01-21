
#pragma once

#include "JuceHeader.h"
// #include <unordered_map>

class Generation : public ControllableContainer
{
public:
    juce_DeclareSingleton(Generation, true);
    Generation();
    ~Generation();

    IntParameter *numLevels;

    enum GrowthMode
    {
        CONSTANT,
        POLYNOMIAL,
        EXPONENTIAL
    };
    EnumParameter *growthEntitiesPerLevel; // constant, polynomial, exponential
    IntParameter *entPerLevNum;
    FloatParameter *entPerLevA;
    FloatParameter *entPerLevB;
    IntParameter *entPerLevUncert;
    
    // old paramaters, to compile, remove later
    IntParameter *entitiesPerLevel;
    Point2DParameter *concentRange;
    Point2DParameter *entitiesPerLevelRange;



    IntParameter *maxReactionsPerEntity;

    FloatParameter *maxDestructionRate;
    FloatParameter *maxCreationRate;

    FloatParameter *energyPerLevel;
    FloatParameter *energyUncertainty;
    FloatParameter *maxEnergyBarrier;

    IntParameter *avgNumShow;
    // FloatParameter *minG;
    // FloatParameter *maxG;
    // FloatParameter *maxAddGstar;

    void onContainerParameterChanged(Parameter *p) override;
};
