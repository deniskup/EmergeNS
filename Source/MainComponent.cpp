#include "MainComponent.h"

//==============================================================================
MainComponent::MainComponent()
{
    setSize(600, 400);

    shouldRepaint = false;
    simul = Simulation::getInstance();

    addAndMakeVisible(maxStepsSlider);
    maxStepsSlider.setRange(1, 100, 1);
    maxStepsSlider.setValue(50);
    maxStepsSlider.setTextValueSuffix(" Steps");
    maxStepsSlider.addListener(this);

    addAndMakeVisible(maxStepsLabel);
    maxStepsLabel.setText("MaxSteps ", juce::dontSendNotification);
    maxStepsLabel.attachToComponent(&maxStepsSlider, true); // [4]
    DBG("Test");
    startTimerHz(50);

    simul->addChangeListener(this);
    simul->start();
    
}

MainComponent::~MainComponent()
{
}

//==============================================================================
void MainComponent::paint(juce::Graphics &g)
{
    // (Our component is opaque, so we must completely fill the background with a solid colour)
    g.fillAll(getLookAndFeel().findColour(juce::ResizableWindow::backgroundColourId));

    g.setFont(juce::Font(16.0f));
    g.setColour(juce::Colours::white);

    Rectangle<int> r = getLocalBounds().withTop(maxStepsSlider.getBottom() + 10);

    for (auto &ent : simul->entities)
    {
        g.drawText("Ent " + String(ent->id) + " : " + String(ent->concent), r.removeFromTop(20), juce::Justification::centred, true);
        r.removeFromTop(8);
    }
}

void MainComponent::resized()
{
    // This is called when the MainComponent is resized.
    // If you add any child components, this is where you should
    // update their positions.
    auto sliderLeft = 120;
    maxStepsSlider.setBounds(sliderLeft, 20, getWidth() - sliderLeft - 10, 20);
}

void MainComponent::sliderValueChanged(Slider *slider)
{
    simul->maxSteps = slider->getValue();
    shouldRepaint = true;
}

void MainComponent::timerCallback()
{
    if (!shouldRepaint)
        return;

    repaint();
    shouldRepaint = false;
}

void MainComponent::changeListenerCallback(ChangeBroadcaster *)
{
    shouldRepaint = true;
    DBG("newstep");
    for (auto &ent : simul->entities){
        DBG("Ent " + String(ent->id) + " : " + String(ent->concent));
    }
}
