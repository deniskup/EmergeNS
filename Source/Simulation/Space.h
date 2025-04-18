
#pragma once

#include "JuceHeader.h"
#define CACROB_PRECISION 5

#include "EntityManager.h"

using namespace juce;
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
    neighbours.add(getGlobalIndex(tilSize, moduloSum(rowIndex, -1, tilSize), colIndex));
    neighbours.add(getGlobalIndex(tilSize, moduloSum(rowIndex, -1, tilSize), moduloSum(colIndex, -1, tilSize)));
    neighbours.add(getGlobalIndex(tilSize, rowIndex, moduloSum(colIndex, -1, tilSize)));
    neighbours.add(getGlobalIndex(tilSize, rowIndex, moduloSum(colIndex, 1, tilSize)));
    neighbours.add(getGlobalIndex(tilSize, moduloSum(rowIndex, 1, tilSize), colIndex));
    neighbours.add(getGlobalIndex(tilSize, moduloSum(rowIndex, 1, tilSize), moduloSum(colIndex, 1, tilSize)));
  }
  
  Array<int> neighbours;
  Point<float> center;
  int id;
  int rowIndex;
  int colIndex;
};



class Space : public ControllableContainer
{
public:
    juce_DeclareSingleton(Space, true);
    Space();
    //Space(Simulation *simul);
    ~Space();

    //Simulation * simul;
   
    IntParameter * tilingSize; 
  
    FloatParameter * diffConstant;
  
    int previousTiling;
  
    int nPatch;
      
    void onContainerParameterChanged(Parameter *p) override;
    
    void afterLoadJSONDataInternal() override;
  
    Array<Patch> spaceGrid;


  //   class SettingsListener
  // {
  // public:
  //   virtual ~SettingsListener() {
  //   virtual void updateSettingsUI(Settings *){};
  // };

  // ListenerList<SettingsListener> listeners;
  // void addSettingsListener(SettingsListener *newListener) { listeners.add(newListener); }
  // void removeSettingsListener(SettingsListener *listener) { listeners.remove(listener); }
};



