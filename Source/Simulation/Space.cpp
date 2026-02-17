#include "Space.h"
#include "Simulation.h"


juce_ImplementSingleton(Space);

Space::Space() : ControllableContainer("Space"), Thread("Space"), spaceNotifier(1000)
{
  //cout << "simul(1)->isSpace : " << simul->isSpace->boolValue() << endl;
  tilingSize = addIntParameter("Tiling size", "Tiling size", 1, 1);
  previousTiling = tilingSize->intValue();
  diffConstant = addFloatParameter("Diffusion constant", "Diffusion Constant", 0.01, 0.f);
  realTime = addBoolParameter("Real time", "Show time dynamics in real time", false);
  timeOfReplay = addFloatParameter("Replay Time", "Replay Time", 5., 1.f, 100.f);
  initGridAtStartValues = addTrigger("Init. grid at start values", "Init. grid at start values", 0.01, 0.f);
  replay = addTrigger("Replay", "Replay", 0.01, 0.f);
  replayProgress = addIntParameter("Replay progress", "Replay progress", 0, 0, 100);
  replayProgress->setControllableFeedbackOnly(true);
  nPatch = 1;
  initNewSpaceGrid();
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

Patch Space::getPatchForRowCol(int row, int col)
{
  int globalindex = row * tilingSize->intValue() + col;
  jassert(globalindex < spaceGrid.size());
  return spaceGrid.getUnchecked(globalindex);
}



void Space::initNewSpaceGrid()
{
  // loop over number of rows to draw
  for (int r=0; r<tilingSize->intValue(); r++)
  {
    //float shiftX = (r%2==0 ? 0. : 0.5*width*std::sqrt(3));
    // loop over columns
    for (int c=0; c<tilingSize->intValue(); c++)
    //for (int r=0; r<1; r++)
    {
      // update grid in Space instance
      Patch patch;
      patch.id = r*tilingSize->intValue() + c;
      patch.rowIndex = r;
      patch.colIndex = c;
      patch.setNeighbours(tilingSize->intValue());
      //Point p(cX, cY);
      //patch.center = p;
      spaceGrid.add(patch);
    }
  }
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
    // init a new one
    initNewSpaceGrid();
    
    // call simulation instance to update all arrays in simu
    //cout << "calling updateSpaceGridSizeInSimu()" << endl;
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
    
    
    // I define the checkpoints by imposing that the time between two frames equals timeframe, chosen to be below the
    // human eye retina persistence (0.1s).
    float timeframe = 0.05;
    int checkPoint = timeframe * (float) Simulation::getInstance()->dynHistory->concentHistory.size() / timeOfReplay->floatValue();
    checkPoint = jmax(1, checkPoint);
    
    cout << "Npoints total = " << Simulation::getInstance()->dynHistory->concentHistory.size() << endl;
    cout << "checkpoint = " << checkPoint << endl;
    
    // only keep concentration snapshots consistent with checkpoints calculated
    for (int k=0; k<Simulation::getInstance()->dynHistory->concentHistory.size(); k++)
    {
      if (k % checkPoint != 0)
        continue;
      concMovie.add(Simulation::getInstance()->dynHistory->concentHistory.getUnchecked(k).conc);
      //cout << "added vector conc for step " << Simulation::getInstance()->dynHistory->concentHistory.getUnchecked(k).step << endl;
    }
    
    cout << "number of snapshots for replay : " << concMovie.size() << endl;
    
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
    
    replayProgress->setValue((int)(((sn+1) * 100) / (concMovie.size())));
    
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
    
    /*
    if (concMovie.getUnchecked(sn).size() != entityColours.size())
    {
      cout << "SHOULD NOT HAPPEN. In step " << sn << endl;
      ConcentrationGrid cg = concMovie.getUnchecked(sn);
      for (auto & [key, val] : cg)
      {
        cout << "patch " << key.first << " ; idSAT " << key.second << " ; conc " << val << endl;
      }
      stopThread(10);
    }
    */
    
    // call space event
    //cout << "space event for step " << sn << ". conc grid size : " << concMovie.getUnchecked(sn).size() << endl;
    spaceNotifier.addMessage(new SpaceEvent(SpaceEvent::NEWSTEP, this, sn, concMovie.getUnchecked(sn), entityColours));
    
  }
  
  spaceNotifier.addMessage(new SpaceEvent(SpaceEvent::FINISHED, this, sn, {}, {}));
  
  concMovie.clear();

  LOG("--------- End thread ---------");
  
}







