
#pragma once

#include "JuceHeader.h"
#define CACROB_PRECISION 5
#include "EntityManager.h"
#include "SimulationHelpers.h"

#include "EntityManager.h"
#include "SimulationHelpers.h"

//using namespace juce;
using namespace std;

class Simulation;


class Patch
{
  public:

  Patch(){};
  ~Patch(){};
  
  int moduloSum(int a, int b, int tilSize)
  {
    int sum = a + b;
    while (sum<0)
      sum += tilSize;
    
    return (sum%(tilSize));
  }
  
  int getGlobalIndex(int til, int row, int col)
  {
    return (til*row + col);
  }
  
  // neighbours of (i,j) are (i-1,j) , (i-1, j-1), (i, j-1), (i, j+1), (i+1, j), (i+1, j+1)
  void setNeighbours(int tilSize)
  {
    neighbours.clear();
    if (tilSize==1)
      return;
    if (tilSize != 2)
    {
      neighbours.add(getGlobalIndex(tilSize, moduloSum(rowIndex, -1, tilSize), colIndex));
      neighbours.add(getGlobalIndex(tilSize, moduloSum(rowIndex, -1, tilSize), moduloSum(colIndex, -1, tilSize)));
      neighbours.add(getGlobalIndex(tilSize, rowIndex, moduloSum(colIndex, -1, tilSize)));
      neighbours.add(getGlobalIndex(tilSize, rowIndex, moduloSum(colIndex, 1, tilSize)));
      neighbours.add(getGlobalIndex(tilSize, moduloSum(rowIndex, 1, tilSize), colIndex));
      neighbours.add(getGlobalIndex(tilSize, moduloSum(rowIndex, 1, tilSize), moduloSum(colIndex, 1, tilSize)));
    }
    else
    {
      if (id == 0)
        neighbours.add(1);
      else
        neighbours.add(0);
    }
  }
  
  juce::Array<int> neighbours;
  juce::Point<float> center;
  int id;
  int rowIndex;
  int colIndex;
};



class Space : public ControllableContainer, public juce::Thread
{
public:
    juce_DeclareSingleton(Space, true);
    Space();
    //Space(Simulation *simul);
    ~Space();

    //Simulation * simul;
   
    IntParameter * tilingSize; 
  
    FloatParameter * diffConstant;
 
    FloatParameter * timeOfReplay;
  
    BoolParameter * realTime;
  
    Trigger * initGridAtStartValues;
  
    Trigger * replay;
  
    IntParameter* replayProgress;
  
    Trigger * cancelPatchSelection;
  
    StringParameter * strPatchSelected;
  
    int previousTiling;
  
    int nPatch;
  
    Patch getPatchForRowCol(int row, int col);
  
    void initNewSpaceGrid();
      
    void onContainerParameterChanged(Parameter *p) override;
  
    void onContainerTriggerTriggered(Trigger *t) override;
  
    void run() override;
  
    juce::Array<Patch> spaceGrid;
  
    juce::Array<int> patchSelected;

  private:
    
  juce::Array<ConcentrationGrid> concMovie;
  
  
  
  
  public:
  
  // ASYNC
  class SpaceEvent
  {
  public:
    enum Type
    {
      UPDATE_GRID,
      WILL_START,
      NEWSTEP,
      FINISHED,
    };


    SpaceEvent(Type t,
      Space* space,
      int curStep = 0,
      ConcentrationGrid entityValues = {},
      juce::Array<juce::Colour> entityColors = juce::Array<juce::Colour>())
      : type(t), space(space), curStep(curStep), entityValues(entityValues), entityColors(entityColors)
    {
    }

    Type type;
    Space* space;
    int curStep;
    ConcentrationGrid entityValues;
    juce::Array<juce::Colour> entityColors;
  };

  QueuedNotifier<SpaceEvent> spaceNotifier;
  typedef QueuedNotifier<SpaceEvent>::Listener AsyncSpaceListener;

  void addAsyncSpaceListener(AsyncSpaceListener* newListener) { spaceNotifier.addListener(newListener); }
  void addAsyncCoalescedSpaceListener(AsyncSpaceListener* newListener) { spaceNotifier.addAsyncCoalescedListener(newListener); }
  void removeAsyncSpaceListener(AsyncSpaceListener* listener) { spaceNotifier.removeListener(listener); }

};



