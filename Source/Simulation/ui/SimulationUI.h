
#pragma once

#include "../Simulation.h"

class SimulationUI : public ShapeShifterContentComponent,
                     public Simulation::SimulationListener,
                     public Timer
{
public:
    SimulationUI();
    ~SimulationUI();

    Simulation *simul;
    bool shouldRepaint;
    Array<Array<float>> entityHistory;
    Array<SimEntity*> entityRefs;

    std::unique_ptr<IntStepperUI> maxStepsUI;
    std::unique_ptr<IntSliderUI> curStepUI;
    std::unique_ptr<TriggerUI> startUI;
    std::unique_ptr<TriggerUI> cancelUI;

    void paint(juce::Graphics &) override;
    void resized() override;
    void timerCallback() override;
    bool keyPressed(const KeyPress &e) override;

    void newStep(Simulation *) override;
    void simulationStarted(Simulation *) override;
    void simulationFinished(Simulation *) override;
    

    static SimulationUI *create(const String &name) { return new SimulationUI(); }
};