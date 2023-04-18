
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
        PROPORTION,
        PROPREACTIONS
    };

   /* enum GrowthReactionMode
    {
        PERENTITY,
        PERCENTAGE
    };
  */
    EnumParameter *growthEntitiesPerLevel; // constant, polynomial, proportion of total
    IntRangeParameter *entPerLevNum;
    FloatParameter *entPerLevA;
    FloatParameter *entPerLevB;
    IntParameter *entPerLevUncert;
    FloatParameter *propEntities; //proportion of entities to include
    
    // old paramaters, to compile, remove later
    IntParameter *entitiesPerLevel;
    Point2DParameter *concentRange;
    Point2DParameter *entitiesPerLevelRange;
   // IntParameter *maxReactionsPerEntity;

    //EnumParameter *growthReactionsPerLevel; //#perEntity, % of total
    IntRangeParameter *reactionsPerEntity;
    FloatParameter *propReactions; //proportion of reactions to include

    FloatParameter *maxDestructionRate;
    FloatParameter *maxCreationRate;
    //ODO add variances

    FloatParameter *energyPerLevel;
    FloatParameter *energyUncertainty;
    FloatParameter *maxEnergyBarrier;

    BoolParameter *showAll;
    IntParameter *avgNumShow;
    // FloatParameter *minG;
    // FloatParameter *maxG;
    // FloatParameter *maxAddGstar;

    void onContainerParameterChanged(Parameter *p) override;

    class GenerationListener
  {
  public:
    virtual ~GenerationListener() {}
    virtual void updateGenUI(Generation *){};
  };

  ListenerList<GenerationListener> listeners;
  void addGenerationListener(GenerationListener *newListener) { listeners.add(newListener); }
  void removeGenerationListener(GenerationListener *listener) { listeners.remove(listener); }
};
