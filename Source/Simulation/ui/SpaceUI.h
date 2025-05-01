
#pragma once

#include "../Space.h"
#include "SimulationUI.h"


class SpaceUI : public ShapeShifterContentComponent
            //public Settings::SettingsListener
{
public:
    SpaceUI();
    ~SpaceUI();

    Space * space;
    
    std::unique_ptr<GenericControllableContainerEditor> editorUI;

    void resized() override;
  
    void paint(juce::Graphics &) override;
  
    void paintOneHexagon(juce::Graphics &, float startX, float startY, float width);

    static SpaceUI *create(const String &name) { return new SpaceUI(); }
  
    int getPatchIDAtPosition(const juce::MouseEvent&);
  
    void mouseDown(const juce::MouseEvent& event) override;
  
    //void updateSettingsUI(Settings *) override;
  
    Rectangle<int> spaceBounds;
  
    int previousTil;
  
    float width; // width of hexagons in the grid
  

};
