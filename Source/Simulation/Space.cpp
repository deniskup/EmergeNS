#include "Space.h"
#include "Simulation.h"


juce_ImplementSingleton(Space);

Space::Space() : ControllableContainer("Space"), Thread("Space")
{
  //cout << "simul(1)->isSpace : " << simul->isSpace->boolValue() << endl;
  tilingSize = addIntParameter("Tiling size", "Tiling size", 1, 1);
  previousTiling = tilingSize->intValue();
  diffConstant = addFloatParameter("Diffusion constant", "Diffusion Constant", 0.01, 0.f);
  timeOfReplay = addFloatParameter("Time for dynamics replay", "Time for dynamics replay", 5., 1.f, 100.f);
  replay = addTrigger("Replay", "Replay", 0.01, 0.f);
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



void Space::onContainerTriggerTriggered(Trigger *t)
{
  if (t == replay)
  {
    int checkPoint = Simulation::getInstance()->maxSteps / Simulation::getInstance()->pointsDrawn->intValue();
    checkPoint = jmax(1, checkPoint);
    steps.clear();
    timestep = timeOfReplay->floatValue() / (float) Simulation::getInstance()->pointsDrawn->intValue();
    for (int k=0; k<Simulation::getInstance()->dynHistory->concentHistory.size(); k++)
    {
      if (k % checkPoint == 0)
        steps.add(k);
    }
    stopThread(100);
    startThread();
  }
}



void Space::run()
{
  auto startTime = std::chrono::steady_clock::now();
  
  // loop over concentration dynamics
  for (int k=0; k<steps.size(); k++)
  {
    int st = steps[k];
    
    auto currentTime = std::chrono::steady_clock::now();
    auto elapsed = std::chrono::duration_cast<std::chrono::milliseconds>(currentTime - startTime).count();
    
    // if timestep - elapsed > 0, call wait(timestep - elapsed)
    // beware of types and units
    
    // Think about the following :
   // SpaceUI should have a comparable functions as SImulationUI and PACUI to update patches colors when a simulation event is called
    // same for this specific thread, though I should leave unchanged PACUI and SimulationUI.
    // Maybe best way is to implement a SpaceEvent and call it independently of SimulationEvent ?

    // Once this is done, Need some thinking about the colour of a patch at each event. See refs in rivoire and bunin to see how to do.
    
    // see how to handle change colours in SpaceUI paint(). Maybe worth it to consider not redrawing the spacegrid for each space event ?
    
    /*
     d'après chatGPT
     using namespace std::chrono;

     // On capture le temps de départ
         auto startTime = steady_clock::now();

         for (int i = 0; i < numIterations; ++i)
         {
             // Simuler un travail (tu peux l’enlever si t’as ton propre taf à faire ici)
             std::this_thread::sleep_for(milliseconds(100 + i * 10)); // ça groove doucement

             // Temps actuel
             auto currentTime = steady_clock::now();

             // Durée écoulée depuis le début
             auto elapsed = duration_cast<milliseconds>(currentTime - startTime).count();

             std::cout << "Itération " << i << " - Temps écoulé depuis le début : " << elapsed << " ms" << std::endl;
         }

     */
    
  }
  
  steps.clear();
  stopThread(100);
 
  
}







