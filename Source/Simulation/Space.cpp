#include "Space.h"


juce_ImplementSingleton(Space);

Space::Space() : ControllableContainer("Space")
{

  tilingSize = addIntParameter("Tiling size", "Tiling size", 1, 1);
  previousTiling = tilingSize->intValue();

}

Space::~Space()
{
}

void Space::onContainerParameterChanged(Parameter *p)
{
  if (p == tilingSize)
  {
    int newtiling = p->intValue();
    if (newtiling%2==0) // if new tiling is even number, change it to closest odd number
    {
      if (newtiling>previousTiling)
      {
        previousTiling = newtiling+1;
        tilingSize->setValue(var(newtiling+1));
      }
      else if (newtiling<previousTiling)
      {
        previousTiling = newtiling-1;
        tilingSize->setValue(var(newtiling-1));
      }
    }
  }
  
}



void Space::afterLoadJSONDataInternal()
{
  //updateNoiseParameter();
}


