
#pragma once

#include "../Space.h"
#include "SimulationUI.h"


class SpaceUI : public ShapeShifterContentComponent,
                public Simulation::AsyncSimListener,
                public Timer,
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
  
    void paintOneHexagon(juce::Graphics &, float startX, float startY, float width);

    static SpaceUI *create(const String &name) { return new SpaceUI(); }
  
    int getPatchIDAtPosition(const juce::Point<int>&);
  
    void mouseDown(const juce::MouseEvent& event) override;
  
    //void updateSettingsUI(Settings *) override;
    void timerCallback() override;
  
    void newMessage(const Simulation::SimulationEvent &ev) override;
  
    void newMessage(const ContainerAsyncEvent &e) override;


  
    Rectangle<int> spaceBounds;
  
    int previousTil;
  
    float width; // width of hexagons in the grid
  
    bool shouldRepaint = false;
  
    bool gridIsAlreadyDrawn = false;
  
    float pixOriginX;
    float pixOriginY;
  
  
    //Array<Array<float>> entityHistory;
    Array<ConcentrationGrid> entityHistory;
    Array<Colour> entityColors;
  

};
