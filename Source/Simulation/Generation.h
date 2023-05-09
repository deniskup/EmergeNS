
#pragma once

#include "JuceHeader.h"
// #include <unordered_map>

class Generation : public ControllableContainer
{
public:
    juce_DeclareSingleton(Generation, true);
    Generation();
    ~Generation();

    //change to IntRangeParameter for interval
    IntParameter *primEntities; 
    IntParameter *numLevels;


    enum GrowthMode
    {
        CONSTANT,
        POLYNOMIAL,
      //  PROPORTION,
        PROPREACTIONS
    };

   /* enum GrowthReactionMode
    {
        PERENTITY,
        PERCENTAGE
    };
  */
    EnumParameter *growthEntitiesPerLevel; // constant, polynomial, proportion of total
    IntParameter *entPerLevNum;
    FloatParameter *entPerLevA;
    FloatParameter *entPerLevB;
    IntParameter *entPerLevUncert;
    //FloatParameter *propEntities; //proportion of entities to include
    
    IntParameter *entitiesPerLevel;
    Point2DParameter *initConcent;
    Point2DParameter *entitiesPerLevelRange;
   // IntParameter *maxReactionsPerEntity;

    //EnumParameter *growthReactionsPerLevel; //#perEntity, % of total
    IntParameter *reactionsPerEntity;
    FloatParameter *propReactions; //proportion of reactions to include

    //param+variance
    Point2DParameter *destructionRate;
    Point2DParameter *creationRate;
    Point2DParameter *energyPerLevel;
    Point2DParameter *energyBarrier;

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
