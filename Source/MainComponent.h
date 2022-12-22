#pragma once

#include <JuceHeader.h>
#include "Data.h"

using namespace juce;

//==============================================================================
/*
    This component lives inside our window, and this is where you should put all
    your controls and content.
*/
class MainComponent : public juce::Component,
                      public Slider::Listener,
                      public ChangeListener,
                      public Timer

{
public:
    //==============================================================================
    MainComponent();
    ~MainComponent();

    //==============================================================================
    void paint(juce::Graphics &) override;
    void resized() override;
    void sliderValueChanged(Slider *slider) override;
    void timerCallback() override;

    void changeListenerCallback(ChangeBroadcaster *);

private:
    //==============================================================================
    // Your private member variables go here...
    juce::Slider maxStepsSlider;
    juce::Label maxStepsLabel;
    Simulation *simul;
    bool shouldRepaint;
    JUCE_DECLARE_NON_COPYABLE_WITH_LEAK_DETECTOR(MainComponent)
};
