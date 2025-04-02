
#pragma once

#include "../Space.h"

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
  
    void mouseDown(const juce::MouseEvent& event) override;
  
    //void updateSettingsUI(Settings *) override;
  
    Rectangle<int> spaceBounds;
  
    int previousTil;
  
  


};
