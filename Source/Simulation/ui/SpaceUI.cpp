
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
  spaceBounds = getLocalBounds().withTop(50).withTrimmedBottom(10).withLeft(20).reduced(50);
  
  int til = space->tilingSize->intValue();
  if (til != previousTil)
  {
    repaint();
    previousTil = til;
  }
  
  //std::cout << "Will paint space window with tiling value : " << til << std::endl;
  
  // start is at upper left corner
  float width = 0.5*std::min(spaceBounds.getWidth(), spaceBounds.getHeight()) / (float) til;
  float centerX = spaceBounds.getX() + width;
  float centerY = spaceBounds.getY() + width;

  // loop over number of columns to draw
  for (int c=0; c<til; c++)
  //for (int c=0; c<2; c++)
  {
    // loop over rows
    for (int r=0; r<til; r++)
    //for (int r=0; r<1; r++)
    {
      float shiftX = (r%2==0 ? 0. : 0.5*width*std::sqrt(3));
      float cX = centerX + std::sqrt(3)*width*c + shiftX;
      float cY = centerY + 1.5*width*r;
      paintOneHexagon(g, cX, cY, width);
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
 In class juce::mouseEvent()
  Point< int > getPosition ()
 
 Retrieve position of closest hexagon center on a click
 Should do nothing if the click occurs outside of space grid, maybe relying on color background ?
 */

void SpaceUI::mouseDown(const juce::MouseEvent& event)
{
  std::cout << "Mouse click at: " << event.position.toString() << std::endl;
}
