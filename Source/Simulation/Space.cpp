#include "Space.h"


juce_ImplementSingleton(Space);

Space::Space() : ControllableContainer("Space")
{

  tilingSize = addIntParameter("Tiling size", "Tiling size", 1, 1);

}

Space::~Space()
{
}

void Space::onContainerParameterChanged(Parameter *p)
{
  if (p == tilingSize)
  {
   // updateNoiseParameter();
  }
  
}



void Space::afterLoadJSONDataInternal()
{
  //updateNoiseParameter();
}


