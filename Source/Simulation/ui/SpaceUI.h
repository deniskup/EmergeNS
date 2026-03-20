
#pragma once

#include "../Space.h"
#include "SimulationUI.h"



class SpaceUI : public ShapeShifterContentComponent,
                public Simulation::AsyncSimListener,
                public Space::AsyncSpaceListener,
                public juce::Timer,
                public ContainerAsyncListener
{
public:
    SpaceUI();
    ~SpaceUI();

    Space * space;
  
    Simulation * simul;
    
    std::unique_ptr<GenericControllableContainerEditor> editorUI;

    void resized() override;
  
    void paint(juce::Graphics &) override;
    
    void drawSpaceGrid(juce::Graphics &);
  
    void paintOneHexagon(juce::Graphics &, float startX, float startY, float width);

    static SpaceUI *create(const juce::String &name) { return new SpaceUI(); }
  
    int getPatchIDAtPosition(const juce::Point<int>&);
  
    void mouseDown(const juce::MouseEvent& event) override;
  
    //void updateSettingsUI(Settings *) override;
    void timerCallback() override;
  
    void newMessage(const Simulation::SimulationEvent &ev) override;
  
    void newMessage(const Space::SpaceEvent &ev) override;
  
    void newMessage(const ContainerAsyncEvent &e) override;


private:
  
    std::unordered_map<int, juce::Path> hexagons; // map drawn hexagons (paths) to their patch id
  
    juce::Rectangle<int> spaceBounds;
  
    int previousTil;
  
    float width; // width of hexagons in the grid
  
    bool shouldRepaint = false;
  
    bool gridIsAlreadyDrawn = false;
  
    bool useStartConcentrationValues = true;
  
    float pixOriginX;
    float pixOriginY;
  
    unique_ptr<IntSliderUI> replayProgressUI;
  
  
    //Array<Array<float>> entityHistory;
    juce::Array<ConcentrationGrid> entityHistory;
    juce::Array<juce::Colour> entityColors;
  

};
