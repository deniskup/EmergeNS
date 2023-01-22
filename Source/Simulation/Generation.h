
#pragma once

#include "JuceHeader.h"
// #include <unordered_map>

class Generation : public ControllableContainer
{
public:
    juce_DeclareSingleton(Generation, true);
    Generation();
    ~Generation();

    IntRangeParameter *primEntities;
    IntRangeParameter *numLevels;


    enum GrowthMode
    {
        CONSTANT,
        POLYNOMIAL,
        EXPONENTIAL
    };
    EnumParameter *growthEntitiesPerLevel; // constant, polynomial, exponential
    IntRangeParameter *entPerLevNum;
    FloatParameter *entPerLevA;
    FloatParameter *entPerLevB;
    IntParameter *entPerLevUncert;
    
    // old paramaters, to compile, remove later
    IntParameter *entitiesPerLevel;
    Point2DParameter *concentRange;
    Point2DParameter *entitiesPerLevelRange;
   // IntParameter *maxReactionsPerEntity;

    
    IntRangeParameter *reactionsPerEntity;

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

    class GenerationListener
  {
  public:
    virtual ~GenerationListener() {}
    virtual void updateGrowth(Generation *){};
  };

  ListenerList<GenerationListener> listeners;
  void addGenerationListener(GenerationListener *newListener) { listeners.add(newListener); }
  void removeGenerationListener(GenerationListener *listener) { listeners.remove(listener); }
};
