#include "Space.h"
#include "Simulation.h"


juce_ImplementSingleton(Space);

Space::Space() : ControllableContainer("Space")
{
  //cout << "simul(1)->isSpace : " << simul->isSpace->boolValue() << endl;
  tilingSize = addIntParameter("Tiling size", "Tiling size", 1, 1);
  previousTiling = tilingSize->intValue();
  diffConstant = addFloatParameter("Diffusion constant", "Diffusion Constant", 0.01, 0.f);
  nPatch = 1;
}

/*
Space::Space(Simulation * _simul) : ControllableContainer("Space"), simul(_simul)
{
  simul = _simul;
  cout << "flag A" << endl;
  cout << "simul(2)->isSpace : " << Simulation::getInstance()->isSpace->boolValue() << endl;
  Space();
}
*/
Space::~Space()
{
}

void Space::onContainerParameterChanged(Parameter *p)
{
  if (Simulation::getInstance()->state != Simulation::SimulationState::Idle)
  {
    LOG("Cannot change Space parameters while running simulation.");
    return;
  }
  
  if (p == tilingSize)
  {
    //cout << "new tiling size : " << p->intValue() << " and isSpace : " << simul->isSpace << endl;
    //if (!simul->isSpace) // do not update tiling if space is set to false
    if (!Simulation::getInstance()->isSpace->boolValue() && tilingSize->intValue()!=1) // do not update tiling if space is set to false
    {
      LOG("Trying to change tiling size while heterogeneous space is set to false in current simulation.");
      tilingSize->setValue(1);
      return;
    }
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
    nPatch = p->intValue() * p->intValue();
    
    spaceGrid.clear();
    int pid = -1;
    for (auto & patch : spaceGrid)
    {
      pid++;
      patch.id = pid;
      patch.rowIndex = pid / Space::getInstance()->tilingSize->intValue();
      patch.colIndex = pid % Space::getInstance()->tilingSize->intValue();
      patch.setNeighbours(Space::getInstance()->tilingSize->intValue());
    }
    
  }
  
  else if (p == diffConstant)
  {

  }

  
  
}



void Space::afterLoadJSONDataInternal()
{
  //updateNoiseParameter();
}





