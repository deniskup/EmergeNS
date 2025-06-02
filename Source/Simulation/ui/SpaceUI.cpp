
#include "SpaceUI.h"

SpaceUI::SpaceUI() : ShapeShifterContentComponent(Space::getInstance()->niceName),
                           space(Space::getInstance()), simul(Simulation::getInstance())
{
    // option: boucle sur les controllables avec createDefaultUI();
    editorUI.reset(new GenericControllableContainerEditor(space, true));
    addAndMakeVisible(editorUI.get());
  
    simul->addAsyncSimulationListener(this);
    simul->addAsyncContainerListener(this);
    startTimerHz(20);
}

SpaceUI::~SpaceUI()
{
    // settings->removeSettingsListener(this);
  simul->removeAsyncSimulationListener(this);
  simul->removeAsyncContainerListener(this);
}

void SpaceUI::resized()
{
    Rectangle<int> r = getLocalBounds();
    editorUI->setBounds(r.reduced(10));
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
  // should not be called while running simu, because simu needs the space grid which is overriden in this function
  if (Simulation::getInstance()->state != Simulation::SimulationState::Idle)
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
  
  // start is at upper left corner
  //centers.clear();
  float ftil = (float) til;
  Space::getInstance()->spaceGrid.clear();
  width = 0.5*std::min(spaceBounds.getWidth(), spaceBounds.getHeight()) / ftil;
  //float centerX = spaceBounds.getX() + width;
  //float centerY = spaceBounds.getY() + width;
  
  float centerX = spaceBounds.getCentreX() - 0.5*spaceBounds.getWidth()*(1. - pow(0.5, ftil-1.))*0.8;
  float centerY = spaceBounds.getCentreY() - 0.5*spaceBounds.getHeight()*(1. - pow(0.5, ftil-1.))*0.5;
  
  pixOriginX = centerX;
  pixOriginY = centerY;
  
  //cout << "origin : " << pixOriginX << " , " << pixOriginY << endl;
  //cout << "hex. width = " << width << endl;

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
      Patch patch;
      patch.id = r*til + c;
      patch.rowIndex = r;
      patch.colIndex = c;
      patch.setNeighbours(til);
      Point p(cX, cY);
      patch.center = p;
      Space::getInstance()->spaceGrid.add(patch);
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
  
  
  // if the grid is being drawn for the first time, fill hexagons with normal color
  //if (Space::getInstance()->spaceGrid.size()==0)
  if (!gridIsAlreadyDrawn)
  {
    cout << "grid is not drawn" << endl;
    g.setColour(juce::Colours::lightgreen);
    g.fillPath(*hex);
    g.setColour(NORMAL_COLOR);
    g.strokePath(*hex, juce::PathStrokeType(2.0f, juce::PathStrokeType::mitered));
    return;
  }
    
  // retrieve patch ID corresponding to current position
  juce::Point<int> p(centerX, centerY);
  int pid = getPatchIDAtPosition(p);
  
  
  if (pid>=0)
  {
    if (entityHistory.size() > 0)
    {
      
      ConcentrationGrid last = entityHistory.getUnchecked(entityHistory.size()-1); // get last concentration grid
      Array<float> conc; // concentration in current patch only
      for (auto & [key, val] : last)
      {
        if (key.first==pid)
          conc.add(val);
      }
      
      // normalize vector of concentrations
      float tot = 0.;
      for (auto & c : conc)
        tot += c;
      if (tot>0.)
      {
        for (int k=0; k<conc.size(); k++)
          conc.setUnchecked(k, conc[k]/tot);
      }
      // calculate weighted red, green and blue
      uint8_t red = 0;
      uint8_t green = 0;
      uint8_t blue = 0;
      jassert(conc.size() == entityColors.size());
      for (int k=0; k<conc.size(); k++)
      {
        red += conc[k] * entityColors[k].getRed();
        green += conc[k] * entityColors[k].getGreen();
        blue += conc[k] * entityColors[k].getBlue();
      }
      juce::Colour patchcol(red, green, blue);
      //g.setColour(juce::Colours::lightgreen);
      g.setColour(patchcol);
      g.fillPath(*hex);
    }
  }
  
  
  
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
      shouldRepaint = true;
    }
    case Simulation::SimulationEvent::WILL_START:
    {
      if (!simul->redrawPatch)
      {
        entityHistory.clear();
        entityColors.clear();
        repaint();
      }
    }
    break;

    case Simulation::SimulationEvent::STARTED:
    {
      if (!simul->redrawPatch)
      {
        entityColors = ev.entityColors;
        entityHistory.add(ev.entityValues);
      }
    }
    break;

    case Simulation::SimulationEvent::NEWSTEP:
    {
      if (!simul->redrawPatch)
        entityHistory.add(ev.entityValues);
    }
    break;

    case Simulation::SimulationEvent::FINISHED:
    {
        resized();
        repaint();
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


