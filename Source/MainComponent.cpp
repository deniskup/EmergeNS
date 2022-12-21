#include "MainComponent.h"

//==============================================================================
MainComponent::MainComponent()
{
    setSize(600, 400);

    simul = Simulation::getInstance();

    addAndMakeVisible(maxStepsSlider);
    maxStepsSlider.setRange(1, 100,1);
    maxStepsSlider.setValue(50);
    maxStepsSlider.setTextValueSuffix(" Steps");
    maxStepsSlider.addListener(this);

    addAndMakeVisible(maxStepsLabel);
    maxStepsLabel.setText("MaxSteps ", juce::dontSendNotification);
    maxStepsLabel.attachToComponent(&maxStepsSlider, true); // [4]
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
    string varstr = "MaxSteps: " + to_string(simul->maxSteps);
    g.drawText(varstr, getLocalBounds(), juce::Justification::centred, true);
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
}
