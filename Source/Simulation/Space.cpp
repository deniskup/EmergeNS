#include "Space.h"
#include "Simulation.h"


juce_ImplementSingleton(Space);

Space::Space() : ControllableContainer("Space"), Thread("Space"), spaceNotifier(1000)
{
  //cout << "simul(1)->isSpace : " << simul->isSpace->boolValue() << endl;
  tilingSize = addIntParameter("Tiling size", "Tiling size", 1, 1);
  previousTiling = tilingSize->intValue();
  diffConstant = addFloatParameter("Diffusion constant", "Diffusion Constant", 0.01, 0.f);
  timeOfReplay = addFloatParameter("Replay Time", "Replay Time", 5., 1.f, 100.f);
  initGridAtStartValues = addTrigger("Init. grid at start values", "Init. grid at start values", 0.01, 0.f);
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
    
    // clear the already existing grid
    spaceGrid.clear();
    
    // call simulation instance to update all arrays in simu
    Simulation::getInstance()->updateSpaceGridSizeInSimu();
    
    // call space event to redraw an empty grid
    //ConcentrationGrid entityConc;
    Array<Colour> entityColors;
    for (auto & ent : Simulation::getInstance()->entities)
    {
      if (!ent->draw)
        continue;
      entityColors.add(ent->color);
    }
    spaceNotifier.addMessage(new SpaceEvent(SpaceEvent::UPDATE_GRID, this, 0, {}, entityColors));

    
    // assign index coordinates
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
    concMovie.clear();
    stopThread(1);
    
    //cout << "will replay dynamics" << endl;
    
    // I define the checkpoints by imposing that the time between two frames equals timeframe, chosen to be below the
    // human eye retina persistence (0.1s).
    float timeframe = 0.05;
    int checkPoint = timeframe * (float) Simulation::getInstance()->dynHistory->concentHistory.size() / timeOfReplay->floatValue();
    checkPoint = jmax(1, checkPoint);
    
    //cout << "Npoints total = " << Simulation::getInstance()->dynHistory->concentHistory.size() << endl;
    //cout << "checkpoint = " << checkPoint << endl;

    // calculate the effective time between two successive frames
    //float timestep = timeOfReplay->floatValue() / (float) Simulation::getInstance()->pointsDrawn->intValue();
    
    // only keep concentration snapshots consistent with checkpoints calculated
    for (int k=0; k<Simulation::getInstance()->dynHistory->concentHistory.size(); k++)
    {
      if (k % checkPoint != 0)
        continue;
      concMovie.add(Simulation::getInstance()->dynHistory->concentHistory.getUnchecked(k).conc);
    }
    
    //cout << "number of snapshots for replay : " << concMovie.size() << endl;
    
    // launch the replay
    startThread();
  }
  
  else if (t == initGridAtStartValues)
  {
    // retrieve entity colours
    Array<Colour> colours;
    for (auto & ent : Simulation::getInstance()->entities)
    {
      if (!ent->draw)
        continue;
      colours.add(ent->color);
    }
    spaceNotifier.addMessage( new SpaceEvent(SpaceEvent::UPDATE_GRID, this, 0, {}, colours) );
  }
  
}



void Space::run()
{
  LOG("--------- Start thread ---------");
  
  auto startTime = std::chrono::steady_clock::now();
  auto previousTime = startTime;
  
  // calculate time duration (ms) of a single snapshot
  float timesnap = 1000.*timeOfReplay->floatValue() / (float) concMovie.size();
  
  // Call space event for the 1st time
  spaceNotifier.addMessage(new SpaceEvent(SpaceEvent::WILL_START, this));
  
  // Retrieve entity colours
  Array<Colour> entityColours;
  for (auto & ent : Simulation::getInstance()->entitiesDrawn)
  {
    entityColours.add(ent->color);
  }
  
  //cout << "conc movie size = " << concMovie.size() << endl;
  
  // loop over concentration dynamics
  int sn=-1;
  //for (int sn=0; sn<concMovie.size(); sn++)
  while (sn<(concMovie.size()-1) && !threadShouldExit())
  {
    sn++;
    
    // get current time
    auto currentTime = std::chrono::steady_clock::now();
    
    // compare current time to previous time in loop
    const std::chrono::duration<double, std::milli> elapsed = currentTime - previousTime;
    if (elapsed.count() < timesnap)
    {
      float time2wait = timesnap - elapsed.count();
      wait(time2wait);
    }
    // update previous time for next loop iteration
    previousTime = currentTime;
    
    // now I must call space event
    spaceNotifier.addMessage(new SpaceEvent(SpaceEvent::NEWSTEP, this, sn, concMovie.getUnchecked(sn), entityColours));
    
  }
  
  
  concMovie.clear();

  LOG("--------- End thread ---------");
  
}







