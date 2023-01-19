
#pragma once

#include "JuceHeader.h"
// #include <unordered_map>

class Generation : public ControllableContainer
{
public:
    juce_DeclareSingleton(Generation, true);
    Generation();
    ~Generation();

    IntParameter *entitiesPerLevel;

    IntParameter *numLevels;
    IntParameter *maxReactionsPerEntity;
    Point2DParameter *concentRange;
    FloatParameter *maxDestructionRate;
    FloatParameter *maxCreationRate;

    FloatParameter *energyPerLevel;
    FloatParameter *energyUncertainty;
    FloatParameter *maxEnergyBarrier;

    

    IntParameter *avgNumShow;
    // FloatParameter *minG;
    // FloatParameter *maxG;
    // FloatParameter *maxAddGstar;
};
