
#include "SpaceUI.h"

SpaceUI::SpaceUI() : ShapeShifterContentComponent(Space::getInstance()->niceName),
                           space(Space::getInstance()), simul(Simulation::getInstance())
{
    space->replayProgress->hideInEditor = true; 
    editorUI.reset(new GenericControllableContainerEditor(space, true));
    addAndMakeVisible(editorUI.get());
  
    replayProgressUI.reset(space->replayProgress->createSlider());
    replayProgressUI->suffix = "%";
    replayProgressUI->setSize(100, 20);
    addAndMakeVisible(replayProgressUI.get());
    replayProgressUI->customLabel = "Replay progress";
  
    simul->addAsyncSimulationListener(this);
    simul->addAsyncContainerListener(this);
  
    space->addAsyncSpaceListener(this);
    space->addAsyncContainerListener(this);
    startTimerHz(20);
}

SpaceUI::~SpaceUI()
{
    // settings->removeSettingsListener(this);
  simul->removeAsyncSimulationListener(this);
  simul->removeAsyncContainerListener(this);
  
  space->removeAsyncSpaceListener(this);
  space->removeAsyncContainerListener(this);
}

void SpaceUI::resized()
{
    Rectangle<int> r = getLocalBounds();
    editorUI->setBounds(r.reduced(10));
    replayProgressUI->setBounds(r.removeFromBottom(40).reduced(10));
    // r.removeFromTop(10);
    // Rectangle<int> hr = r.removeFromTop(27).reduced(2);
    // // maxStepsUI->setBounds(hr.removeFromLeft(200));
    // numLevelsUI->setBounds(hr);
    // r.removeFromTop(10);
    // entitiesPerLevelUI->setBounds(r.removeFromTop(25));
    // r.removeFromTop(10);
    // maxReactionsPerEntityUI->setBounds(r.removeFromTop(25));
    // r.removeFromTop(10);
    // avgNumShowUI->setBounds(r.removeFromTop(25));
}

// void SettingsUI::updateSettingsUI(Settings *){
// NLOG("SettingsUI","Repaint");
// repaint();
//  editorUI->resetAndBuild();
//}


void SpaceUI::paint(juce::Graphics &g)
{
  
  // should not be called while redrawing a patch or a run
  if (Simulation::getInstance()->redrawPatch || Simulation::getInstance()->redrawRun)
    return;
  
  
  
  g.fillAll(BG_COLOR);
  
  //spaceBounds = getLocalBounds();
  //spaceBounds = getLocalBounds().withTop(50).withTrimmedBottom(10).withLeft(20).reduced(20);
  spaceBounds = getLocalBounds().withTop(50).withLeft(20).reduced(30);
  
  int til = space->tilingSize->intValue();
  if (til != previousTil)
  {
    repaint();
    previousTil = til;
  }
  
  //std::cout << "Will paint space window with tiling value : " << til << std::endl;
  

  drawSpaceGrid(g);
  
  // reset bool to true by default
  if (!useStartConcentrationValues && !space->isThreadRunning())
    useStartConcentrationValues = true;
  //if (useStartConcentrationValues)
   // useStartConcentrationValues = false;

}


void SpaceUI::drawSpaceGrid(juce::Graphics & g)
{
  // start is at upper left corner
  int til = space->tilingSize->intValue();
  float ftil = (float) til;
  
  if (til==1)
    width = 0.35*std::min(spaceBounds.getWidth(), spaceBounds.getHeight()) / ftil;
  else
    width = 0.45*std::min(spaceBounds.getWidth(), spaceBounds.getHeight()) / ftil;
  
  float centerX = spaceBounds.getCentreX() - 0.5*spaceBounds.getWidth()*(1. - pow(0.5, ftil-1.))*0.8;
  float centerY = spaceBounds.getCentreY() - 0.5*spaceBounds.getHeight()*(1. - pow(0.5, ftil-1.))*0.3;
  
  if (til==1)
    centerY += 30;
  
  pixOriginX = centerX;
  pixOriginY = centerY;
  
  //cout << "drawing a space grid with tiling size : " << til << endl;
 // cout << "spacegid in space instance has size : " << space->spaceGrid.size() << endl;
  // loop over number of rows to draw
  for (int r=0; r<til; r++)
  //for (int c=0; c<2; c++)
  {
    float shiftX = (r%2==0 ? 0. : 0.5*width*std::sqrt(3));
    // loop over columns
    for (int c=0; c<til; c++)
    //for (int r=0; r<1; r++)
    {
      //cout << "row, col = " << r << ", " << c << endl;
      float cX = centerX + std::sqrt(3)*width*c + shiftX;
      //float cX = centerX + std::sqrt(3)*width* (c + (float)r/2);
      float cY = centerY + 1.5*width*r;
      paintOneHexagon(g, cX, cY, width);
     // cout << "row, col = (" << r << ", " << c << ") --> [" << cX << " , " << cY << "]" << endl;
      // update grid in Space instance
      //Patch patch;
      //patch.id = r*til + c;
      //patch.rowIndex = r;
      //patch.colIndex = c;
      //patch.setNeighbours(til);
      Point p(cX, cY);
      Patch patch = space->getPatchForRowCol(r, c);
      patch.center = p;
      Space::getInstance()->spaceGrid.setUnchecked(patch.id, patch);
    }
  }
  gridIsAlreadyDrawn = true;
  
}


void SpaceUI::paintOneHexagon(juce::Graphics & g, float centerX, float centerY, float width)
{
  
  g.setColour(NORMAL_COLOR);
  Path * hex = new Path();
  //hex->startNewSubPath(startX, startY);
  
  //for (int i = 0; i < 6; ++i)
  for (int i = 0; i < 6; ++i)
  {
    float angle = juce::MathConstants<float>::pi / 3. * i;
    float x = centerX + width * std::sin(angle);
    float y = centerY + width * std::cos(angle);

    if (i == 0)
      hex->startNewSubPath(x, y);
    else
      hex->lineTo(x, y);
  }
  
  hex->closeSubPath(); // Close the hexagon shape
  
  // retrieve patch ID corresponding to current position
  juce::Point<int> p(centerX, centerY);
  int pid = getPatchIDAtPosition(p);
    
  if (pid>=0)
  {
    Array<float> conc; // concentration in current patch only
    Array<float> maxConcInGrid;
    maxConcInGrid.insertMultiple(0, 0., simul->entities.size());
    if (useStartConcentrationValues /*&& !space->isThreadRunning()*/)
    {
      int ie = -1;
     for (auto & ent : simul->entities)
     {
       ie++;
       if (!ent->draw)
       {
         continue;
       }
       float c = ent->startConcent.getUnchecked(pid);
       conc.add(c);
       for (auto & cp : ent->startConcent)
       {
         if (cp>maxConcInGrid.getUnchecked(ie))
           maxConcInGrid.setUnchecked(ie, cp);
       }
     }
    }
    else
    {
      if (entityHistory.size() > 0)
      {
        ConcentrationGrid last = entityHistory.getUnchecked(entityHistory.size()-1); // get last concentration grid
        for (auto & [patchent, val] : last)
        {
          if (val>maxConcInGrid.getUnchecked(patchent.second))
            maxConcInGrid.setUnchecked(patchent.second, val);
          if (patchent.first!=pid)
            continue;
          if (!simul->getSimEntityForID(patchent.second)->draw)
            continue;
          conc.add(val);
        }
      }
    }
    /*
    // normalize each concentration w.r.t to max concent found in all patches
    Array<float> maxConcInGrid;
    maxConcInGrid.insertMultiple(0, 0., simul->entities.size());
    int ie=-1;
    for (auto & ent : simul->entities)
    {
      ie++;
      for (auto & patch : space->spaceGrid)
      {
        if (ent->concent.getUnchecked(patch.id) > maxConcInGrid.getUnchecked(ie))
          maxConcInGrid.setUnchecked(ie, ent->concent)
      }
    }
    */
    /*
    cout << "In patch #" << pid << endl;
    
    cout << "-- vector of conc -- " << endl;
    for (auto & c : conc)
      cout << c << " ";
    cout << endl;
    */
    
    // normalize vector of concentrations of current patch w.r.t to max of all patches
    // this method does not take into account maxima that would be found later in simulation or that have been found previously.
    // for instance, in a single patch simulation, if X1 = 0.1 and X2 = 0.2 but later W1 = 1 and X2 = 2, they would be shown with the same colour
    for (int k=0; k<conc.size(); k++)
    {
      float max = maxConcInGrid.getUnchecked(k);
      //cout << "max for ent #" << k << " = " << max << endl;
      jassert(max>0.);
      conc.setUnchecked(k, conc.getUnchecked(k)/max);
    }
    /*
    cout << "-- vector of conc norm. to max in space grid -- " << endl;
    for (auto & c : conc)
      cout << c << " ";
    cout << endl;
    */
    
    // normalize vector of concentrations w.r.t its own norm
    float tot = 0.;
    for (auto & c : conc)
      tot += c;
    if (tot>0.)
    {
      for (int k=0; k<conc.size(); k++)
        conc.setUnchecked(k, conc[k]/tot);
    }
    
    /*
    cout << "-- conc noramilzed to unity, using tot = " << tot << endl;
    for (auto & c : conc)
      cout << c << " ";
    cout << endl;
    */
    
    // if entity colors is empty, retrieve entity colors here
    if (entityColors.size()==0)
    {
      for (auto & ent : Simulation::getInstance()->entitiesDrawn)
        entityColors.add(ent->color);
    }
    jassert(conc.size() == entityColors.size());
    
    float red = 0.;
    float green = 0.;
    float blue = 0.;
    //float totWeight = 0.;
    for (int k=0; k<conc.size(); k++)
    {
      red += conc.getUnchecked(k) * entityColors.getUnchecked(k).getFloatRed();
      green += conc.getUnchecked(k) * entityColors.getUnchecked(k).getFloatGreen();
      blue += conc.getUnchecked(k) * entityColors.getUnchecked(k).getFloatBlue();
      //totWeight += conc.getUnchecked(k);
    }
    /*
    if (totWeight>0.f)
    {
        red /= totWeight;
        green /= totWeight;
        blue /= totWeight;
    }
    */
    Colour patchcol = Colour::fromFloatRGBA(red, green, blue, 1.);
    //if (totWeight==0.)
    if (tot==0.)
      patchcol = BG_COLOR;
    g.setColour(patchcol);
    g.fillPath(*hex);
      
    
 /*
    // calculate weighted red, green and blue
    uint8_t red = 0;
    uint8_t green = 0;
    uint8_t blue = 0;
    //cout << conc.size() << " vs " << entityColors.size() << endl;
    if (conc.size() != entityColors.size())
    {
      cout << "issue at step " << entityHistory.size()-1 << " and patch id " << pid << endl;
      cout << "conc vector has wrong size : " << conc.size() << endl;
    }
    jassert(conc.size() == entityColors.size());
    for (int k=0; k<conc.size(); k++)
    {
      red += conc[k] * entityColors[k].getRed();
      green += conc[k] * entityColors[k].getGreen();
      blue += conc[k] * entityColors[k].getBlue();
    }
    juce::Colour patchcol(red, green, blue);
    
    
    //g.setColour(juce::Colours::lightgreen);
    float tot = 0.;
    for (auto & c : conc)
      tot += c;
    
    if (tot==0.)
    {
      cout << "found tot = 0" << endl;
      patchcol = BG_COLOR;
    }
     
    g.setColour(patchcol);
    g.fillPath(*hex);
  */
  
  } // end if pid>=0
  
  
  
  // draw a line around the hexagon
  g.setColour(NORMAL_COLOR);
  g.strokePath(*hex, juce::PathStrokeType(2.0f, juce::PathStrokeType::mitered));
  
}




/*
 returns the patch ID where a mouse click event occured.
 if the click occured outside of the space grid, returns -1
 */
int SpaceUI::getPatchIDAtPosition(const juce::Point<int>& pos)
{
  // convert click position to hexagonal coordinates (pointy top orientation)
  float fcol = (pos.getY()-pixOriginY) * 2. / (3.*width);
  //int temp = round(frow);
  //float omega = (temp%2==0 ? 0. : 0.5);
  //float fcol = (pos.getX()-pixOriginX) / (sqrt(3)*width) - omega;
  float frow = ( (pos.getX()-pixOriginX)/sqrt(3) - (pos.getY()-pixOriginY)/3. ) / width;
  
  // transform to cubic coordinates (x, y, z)
  float x = fcol;
  float z = frow;
  float y = -x -z;
  
  // round them
  int rx = round(x);
  int ry = round(y);
  int rz = round(z);
  
  // Correction pour guarantee x + y + z = 0
  float dx = std::abs(rx - x);
  float dy = std::abs(ry - y);
  float dz = std::abs(rz - z);
  
  // apply corrections
  if (dx > dy && dx > dz)
      rx = -ry - rz;
  else if (dy > dz)
      ry = -rx - rz;
  else
      rz = -rx - ry;
 
  // go back to row and col coordinates
  int row = rx;
  int col = rz;
  
  
  // correction to fit to real coordinates
  col += (int) row/2;
  
  
  //cout << "click at : " << pos.getX() << ", " << pos.getY() << " with width " << width << endl;
  //cout << "frow, fcol : " << frow << " ; " << fcol << endl;
  
  if (row<0 || col<0)
  {
    return -1;
  }
  if (row >= Space::getInstance()->tilingSize->intValue() || col >= Space::getInstance()->tilingSize->intValue())
  {
    return -1;
  }
  
  return (Space::getInstance()->tilingSize->intValue()*row + col);
}




/*
 In class juce::mouseEvent()
  Point< int > getPosition ()
 
 Retrieve position of closest hexagon center on a click
 Does nothing if the click occurs outside of space grid, maybe relying on color background ?
 */

void SpaceUI::mouseDown(const juce::MouseEvent& event)
{
  
  int locatepatch = getPatchIDAtPosition(event.getPosition());
  if (locatepatch>=0)
  {
    EntityManager::getInstance()->setEntityToPatchID(locatepatch);
    Simulation::getInstance()->drawConcOfPatch(locatepatch);
  }
  
}


void SpaceUI::timerCallback()
{
    if (shouldRepaint)
    {
        repaint();
        shouldRepaint = false;
    }
}


void SpaceUI::newMessage(const Simulation::SimulationEvent &ev)
{
    switch (ev.type)
    {
    case Simulation::SimulationEvent::UPDATEPARAMS:
    {
      //shouldRepaint = true;
    }
    case Simulation::SimulationEvent::WILL_START:
    {
      if (!simul->redrawPatch && !simul->redrawRun)
      {
        useStartConcentrationValues = true;
        entityHistory.clear();
        entityColors.clear();
        //repaint();
      }
    }
    break;

    case Simulation::SimulationEvent::STARTED:
    {
      if (!simul->redrawPatch && !simul->redrawRun)
      {
        useStartConcentrationValues = false;
        entityColors = ev.entityColors;
        entityHistory.add(ev.entityValues);
      }
    }
    break;

    case Simulation::SimulationEvent::NEWSTEP:
    {
      if (!simul->redrawPatch && !simul->redrawRun)
      {
        useStartConcentrationValues = false;
        entityHistory.add(ev.entityValues);
        if (space->realTime->boolValue())
          shouldRepaint = true;
      }
       
    }
    break;

    case Simulation::SimulationEvent::FINISHED:
    {
      useStartConcentrationValues = false;
      //resized();
      repaint();
    }
    break;
    }
}



void SpaceUI::newMessage(const Space::SpaceEvent &ev)
{
  switch (ev.type)
  {
    case Space::SpaceEvent::UPDATE_GRID:
    {
      useStartConcentrationValues = true;
      entityColors = ev.entityColors;
      gridIsAlreadyDrawn = false;
      shouldRepaint = true;
      repaint();
    }
    break;
      
    case Space::SpaceEvent::WILL_START:
    {
        useStartConcentrationValues = true;
        entityHistory.clear();
        entityColors.clear();
    }
    break;

    case Space::SpaceEvent::NEWSTEP:
    {
      useStartConcentrationValues = false;
      entityHistory.add(ev.entityValues);
      entityColors = ev.entityColors;
      repaint();
    }
    break;

    case Space::SpaceEvent::FINISHED:
    {
      useStartConcentrationValues = true;
      //resized();
      //repaint();
    }
    break;
    }
}


void SpaceUI::newMessage(const ContainerAsyncEvent &e)
{
    if (e.type == ContainerAsyncEvent::EventType::ControllableFeedbackUpdate)
    {
        if (e.targetControllable == simul->oneColor)
        {
            repaint();
        }
    }
}


