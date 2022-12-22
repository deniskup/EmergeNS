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

    simul->addSimulationListener(this);
}

MainComponent::~MainComponent()
{
}

//==============================================================================
void MainComponent::paint(juce::Graphics &g)
{
    // (Our component is opaque, so we must completely fill the background with a solid colour)
    g.fillAll(Colours::black.brighter(.2f));

    Rectangle<int> r = getLocalBounds().withTop(maxStepsSlider.getBottom() + 10);

    g.setFont(12);
    int index = 0;
    for (auto &ent : simul->entities)
    {
        g.setColour(Colour::fromHSV(index * .32f, 1, 1, 1));
        g.drawText("Ent " + String(ent->id) + " : " + String(ent->concent), r.removeFromTop(20), juce::Justification::centred, true);
        r.removeFromTop(8);
        index++;
    }

    r.reduce(10, 10);
    g.setColour(Colours::white.withAlpha(simul->isThreadRunning() ? .3f : .1f));
    g.fillRoundedRectangle(r.toFloat(), 8);
    g.setColour(Colours::white.withAlpha(.3f));
    g.drawRoundedRectangle(r.toFloat(), 8, 2.f);

    if (!entityHistory.isEmpty())
    {
        float stepX = 1.0f / jmax(simul->maxSteps -1,1);
        float maxConcent = 5;
        OwnedArray<Path> paths;
        for (auto &e : entityHistory[0])
        {
            Path *p = new Path();
            Point<float> ep = r.getRelativePoint(0.f, 1 - e / maxConcent).toFloat();
            p->startNewSubPath(ep);
            paths.add(p); // add one path per entity
        }

        for (int i = 1; i < entityHistory.size(); i++)
        {
            Array<float> values = entityHistory[i];
            for (int j = 0; j < values.size(); j++)
            {
                Point<float> ep = r.getRelativePoint(i * stepX, 1 - values[j] / maxConcent).toFloat();
                // g.drawEllipse(Rectangle<float>(10,10).withCentre(ep), 2.f);
                paths[j]->lineTo(ep);
            }
        }

        for (int i = 0; i < paths.size(); i++)
        {
            g.setColour(Colour::fromHSV(i * .32f, 1, 1, 1));
            g.strokePath(*paths[i], PathStrokeType(2));
        }
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

bool MainComponent::keyPressed(const KeyPress &e)
{
    if (e.getKeyCode() == KeyPress::spaceKey)
    {
        if (simul->isThreadRunning())
            simul->cancel();
        else
        {
            entityHistory.clear();

            int nbEnt = 3;
            Array<Entity *> ents;
            Random r;
            for (int i = 0; i < nbEnt; i++)
                ents.add(new Entity(1, true, r.nextFloat(), r.nextFloat(), r.nextFloat()));


            Reaction *reac = new Reaction({ents[0], ents[1]}, {ents[2]}, .3f, .2f);

            simul->setup(simul->maxSteps, ents, {reac});
            simul->start();
        }
    }

    return false;
}

void MainComponent::newStep(Simulation *)
{
    DBG("New Step");
    Array<float> entityValues;
    for (auto &ent : simul->entities)
    {
        entityValues.add(ent->concent);
        DBG("Ent " + String(ent->id) + " : " + String(ent->concent));
    }
    entityHistory.add(entityValues);

    shouldRepaint = true;
}

void MainComponent::simulationFinished(Simulation *)
{
    DBG("Simulation finished");
}