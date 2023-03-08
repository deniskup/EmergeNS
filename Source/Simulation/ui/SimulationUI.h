
#pragma once

#include "../Simulation.h"

class SimulationUI : public ShapeShifterContentComponent,
                     public Simulation::AsyncSimListener,
                     public Timer,
                     public ContainerAsyncListener
{
public:
    SimulationUI();
    ~SimulationUI();

    Simulation *simul;
    bool shouldRepaint;
    Array<Array<float>> entityHistory;
    Array<Colour> entityColors;

    // std::unique_ptr<IntStepperUI> maxStepsUI;
    std::unique_ptr<FloatParameterLabelUI> dtUI;
    std::unique_ptr<FloatParameterLabelUI> totalTimeUI;
    std::unique_ptr<IntSliderUI> perCentUI;
    std::unique_ptr<FloatParameterLabelUI> maxConcentUI;
    std::unique_ptr<TriggerUI> genUI;
    std::unique_ptr<TriggerUI> startUI;
    std::unique_ptr<TriggerUI> genstartUI;
    std::unique_ptr<TriggerUI> restartUI;
    std::unique_ptr<TriggerUI> cancelUI;
    std::unique_ptr<BoolToggleUI> generatedUI;
    std::unique_ptr<BoolToggleUI> autoScaleUI;
    std::unique_ptr<IntParameterLabelUI> pointsDrawnUI;

    //for diplaying paramaters
    Label paramsLabel;

    // int uiStep;
    Rectangle<int> simBounds;

    // local floatparameter
    // std::unique_ptr<FloatParameter> maxC;
    // std::unique_ptr<FloatParameterLabelUI> maxCUI;

    void paint(juce::Graphics &) override;
    void resized() override;
    void timerCallback() override;
    bool keyPressed(const KeyPress &e) override;

    // void newStep(Simulation *) override;
    // void simulationWillStart(Simulation *) override;
    // void simulationStarted(Simulation *) override;
    // void simulationFinished(Simulation *) override;

    void newMessage(const Simulation::SimulationEvent &e) override;

    void newMessage(const ContainerAsyncEvent &e) override;

    static SimulationUI *create(const String &name) { return new SimulationUI(); }
};