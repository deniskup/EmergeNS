#pragma once

#include "../Simulation.h"
#include "SimulationUI.h"

class PACUI : public ShapeShifterContentComponent,
                     public Simulation::AsyncSimListener,
                     public juce::Timer,
                     public ContainerAsyncListener
                     //public Button::Listener
{
public:
    PACUI();
    ~PACUI();

    Simulation *simul;
    bool shouldRepaint;
    juce::Array<juce::Array<float>> PACsHistory;

    juce::Array<bool> RACList;
    //map<PAC*, bool> RACList;


    juce::Rectangle<int> PACsBounds;

    //oneColor setting

    unique_ptr<BoolToggleUI> oneColorToggle;

    void paint(juce::Graphics &) override;
    void resized() override;
    void timerCallback() override;
    //bool keyPressed(const KeyPress &e) override;


    void newMessage(const Simulation::SimulationEvent &ev) override;

    void newMessage(const ContainerAsyncEvent &e) override;

    static PACUI *create(const juce::String &name) { return new PACUI(); }
};
