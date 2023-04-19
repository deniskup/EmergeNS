#pragma once

#include "../Simulation.h"

class PACUI : public ShapeShifterContentComponent,
                     public Simulation::AsyncSimListener,
                     public Timer
                     //public ContainerAsyncListener
                     //public Button::Listener
{
public:
    PACUI();
    ~PACUI();

    Simulation *simul;
    bool shouldRepaint;
    Array<Array<float>> PACsHistory;

    Array<bool> RACList;


    Rectangle<int> PACsBounds;



    void paint(juce::Graphics &) override;
    void resized() override;
    void timerCallback() override;
    //bool keyPressed(const KeyPress &e) override;


    void newMessage(const Simulation::SimulationEvent &ev) override;

    static PACUI *create(const String &name) { return new PACUI(); }
};