
#include "SpaceUI.h"

SpaceUI::SpaceUI() : ShapeShifterContentComponent(Space::getInstance()->niceName),
                           space(Space::getInstance())
{
    // option: boucle sur les controllables avec createDefaultUI();
    editorUI.reset(new GenericControllableContainerEditor(space, true));
    addAndMakeVisible(editorUI.get());
}

SpaceUI::~SpaceUI()
{
    // settings->removeSettingsListener(this);
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

  // loop over number of rows to draw
  for (int r=0; r<til; r++)
  //for (int c=0; c<2; c++)
  {
    float shiftX = (r%2==0 ? 0. : 0.5*width*std::sqrt(3));
    // loop over columns
    for (int c=0; c<til; c++)
    //for (int r=0; r<1; r++)
    {
      float cX = centerX + std::sqrt(3)*width*c + shiftX;
      float cY = centerY + 1.5*width*r;
      paintOneHexagon(g, cX, cY, width);
      
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

  
  // draw one hexagone
  //float startX = spaceBounds.getCentreX();
  //float startY = spaceBounds.getCentreY();
  //float width = 0.5*std::min(spaceBounds.getWidth(), spaceBounds.getHeight()) / (float) tilt;
  
  

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
  
  //hex->addMouseListener(this, true);
  
  g.setColour(juce::Colours::lightgreen);
  g.fillPath(*hex);
  g.setColour(NORMAL_COLOR);
  g.strokePath(*hex, juce::PathStrokeType(2.0f, juce::PathStrokeType::mitered));

  
  
}

/*
 returns the patch ID where a mouse click event occured.
 if the click occured outside of the space grid, returns -1
 */
int SpaceUI::getPatchIDAtPosition(const juce::MouseEvent& event)
{
  // check that click occured in the space grid and not elsewhere
  juce::Component* clickedComponent = getComponentAt(event.getPosition());
  if (clickedComponent != nullptr)
  {
    // Si tu veux un snapshot pour récupérer la couleur à cet endroit :
    juce::Image snapshot = clickedComponent->createComponentSnapshot(clickedComponent->getLocalBounds());
    juce::Point<int> pointInClickedComponent = clickedComponent->getLocalPoint(this, event.getPosition());

    if (snapshot.isValid() && snapshot.getBounds().contains(pointInClickedComponent))
    {
      juce::Colour colour = snapshot.getPixelAt(pointInClickedComponent.getX(), pointInClickedComponent.getY());
      //cout << "Couleur cliquée : " << colour.toDisplayString(true) << endl;
      if (colour==BG_COLOR)
        return -1;
    }
  }
  
  // find the patch where the click occured
  float dmin = max(spaceBounds.getWidth(), spaceBounds.getHeight());
  int locatepatch = 0;
  for (auto & patch : Space::getInstance()->spaceGrid)
  {
    float d = sqrt( (event.x-patch.center.x)*(event.x-patch.center.x) + (event.y-patch.center.y)*(event.y-patch.center.y) );
    if (d<dmin)
    {
      dmin=d;
      locatepatch = patch.id;
    }
  }
  return locatepatch;
}




/*
 In class juce::mouseEvent()
  Point< int > getPosition ()
 
 Retrieve position of closest hexagon center on a click
 Should do nothing if the click occurs outside of space grid, maybe relying on color background ?
 */

void SpaceUI::mouseDown(const juce::MouseEvent& event)
{
  
  int locatepatch = getPatchIDAtPosition(event);
  if (locatepatch>0)
  {
    EntityManager::getInstance()->setEntityToPatchID(locatepatch);
    Simulation::getInstance()->drawConcOfPatch(locatepatch);
  }
  
}
