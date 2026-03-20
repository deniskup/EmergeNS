#pragma once

#include <JuceHeader.h>
#include "Data.h"

//using namespace juce;

//==============================================================================
/*
    This component lives inside our window, and this is where you should put all
    your controls and content.
*/
class MainComponent : public juce::Component,
                      public juce::Slider::Listener,
                      public Simulation::SimulationListener,
                      public juce::Timer

{
public:
    //==============================================================================
    MainComponent();
    ~MainComponent();

    
    //==============================================================================
    void paint(juce::Graphics &) override;
    void resized() override;
    void sliderValueChanged(juce::Slider *slider) override;
    void timerCallback() override;
    bool keyPressed(const juce::KeyPress& e) override;

    void newStep(Simulation*);
    void simulationFinished(Simulation*);

private:
    //==============================================================================
    // Your private member variables go here...
    juce::Slider maxStepsSlider;
    juce::Label maxStepsLabel;
    Simulation *simul;
    bool shouldRepaint;
    juce::Array<juce::Array<float>> entityHistory;
    JUCE_DECLARE_NON_COPYABLE_WITH_LEAK_DETECTOR(MainComponent)
};
