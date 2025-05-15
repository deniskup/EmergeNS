
#pragma once

#include "../Simulation.h"

// for alignment of simulation and RACs windows
inline int leftMargin = 50;
inline int rightMargin = 40; // previous 40


class SimulationUI : public ShapeShifterContentComponent,
                     public Simulation::AsyncSimListener,
                     public Timer,
                     public ContainerAsyncListener
                     //public Button::Listener
{
public:
    SimulationUI();
    ~SimulationUI();

    Simulation *simul;
    bool shouldRepaint;
    Array<Array<float>> entityHistory;
    Array<Colour> entityColors;
    int runID;

    // TextButton saveSimBT;
    // TextButton loadSimBT;

    // std::unique_ptr<IntStepperUI> maxStepsUI;
    unique_ptr<FloatParameterLabelUI> dtUI;
    unique_ptr<FloatParameterLabelUI> totalTimeUI;
    unique_ptr<IntSliderUI> perCentUI;
    unique_ptr<FloatParameterLabelUI> maxConcentUI;
    unique_ptr<TriggerUI> genUI;
    unique_ptr<TriggerUI> startUI;
    unique_ptr<TriggerUI> genstartUI;
    unique_ptr<TriggerUI> restartUI;
    unique_ptr<TriggerUI> cancelUI;
    //unique_ptr<BoolToggleUI> autoLoadUI;
    unique_ptr<BoolToggleUI> autoScaleUI;
    unique_ptr<IntParameterLabelUI> pointsDrawnUI;
    unique_ptr<BoolToggleUI> ignoreFreeEnergyUI;
    unique_ptr<BoolToggleUI> ignoreBarriersUI;
    unique_ptr<BoolToggleUI> stochasticityUI;
    unique_ptr<BoolToggleUI> detectEqUI;
    unique_ptr<FloatParameterLabelUI> epsilonEqUI;

    unique_ptr<EnumParameterUI> setCACUI;
    unique_ptr<EnumParameterUI> setSteadyStateUI;
    unique_ptr<EnumParameterUI> setRunUI;

    //for diplaying paramaters
    Label paramsLabel;

    // int uiStep;
    Rectangle<int> simBounds;
  
    // to draw axis of concentration VS time
    int nticks = 3;
    int markwidth = 6;
    int markheight = 3;

    // local floatparameter
    // std::unique_ptr<FloatParameter> maxC;
    // std::unique_ptr<FloatParameterLabelUI> maxCUI;

    int firstLineHeight=30; //Height of the first line of buttons
    int secondLineHeight=30; //Height of the second line of buttons

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

    //void buttonClicked(Button* b) override;

    static SimulationUI *create(const String &name) { return new SimulationUI(); }
};
