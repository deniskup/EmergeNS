
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

    
    IntParameter *avgNumShow;
    // FloatParameter *minG;
    // FloatParameter *maxG;
    // FloatParameter *maxAddGstar;
};
