
#include "SimulationUI.h"

SimulationUI::SimulationUI() : ShapeShifterContentComponent(Simulation::getInstance()->niceName),
                               simul(Simulation::getInstance())
{
    maxStepsUI.reset(simul->maxSteps->createStepper());
    curStepUI.reset(simul->curStep->createSlider());
    startUI.reset(simul->startTrigger->createButtonUI());
    cancelUI.reset(simul->cancelTrigger->createButtonUI());

    addAndMakeVisible(maxStepsUI.get());
    addAndMakeVisible(curStepUI.get());
    addAndMakeVisible(startUI.get());
    addAndMakeVisible(cancelUI.get());

    startTimerHz(30);
    simul->addSimulationListener(this);
}

SimulationUI::~SimulationUI()
{
    simul->removeSimulationListener(this);
}

//==============================================================================
void SimulationUI::paint(juce::Graphics &g)
{
    // (Our component is opaque, so we must completely fill the background with a solid colour)
    g.fillAll(BG_COLOR);

    Rectangle<int> r = getLocalBounds().withTop(30);

    g.setFont(12);
    int index = 0;
    for (auto &ent : simul->entities)
    {
        // g.setColour(Colour::fromHSV(index * .32f, 1, 1, 1));
        // g.drawText("Ent " + String(ent->id) + " : " + String(ent->concent), r.removeFromTop(20), juce::Justification::centred, true);
        // r.removeFromTop(8);
        index++;
    }

    r.reduce(10, 10);
    g.setColour(Colours::white.withAlpha(simul->isThreadRunning() ? .1f : .005f));
    g.fillRoundedRectangle(r.toFloat(), 8);
    g.setColour(Colours::white.withAlpha(.3f));
    g.drawRoundedRectangle(r.toFloat(), 8, 2.f);

    if (!entityHistory.isEmpty())
    {
        float stepX = 1.0f / jmax(simul->maxSteps->intValue() - 1, 1);
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
        jassert(entityRefs.size() >= paths.size());
        for (int i = 0; i < paths.size(); i++)
        {
            g.setColour(entityRefs[i]->color);
            g.strokePath(*paths[i], PathStrokeType(1));
        }
    }
}

void SimulationUI::resized()
{
    Rectangle<int> hr = getLocalBounds().removeFromTop(24).reduced(2);
    maxStepsUI->setBounds(hr.removeFromLeft(200));
    hr.removeFromLeft(10);
    curStepUI->setBounds(hr.removeFromLeft(150));
    hr.removeFromLeft(10);
    startUI->setBounds(hr.removeFromLeft(100));
    hr.removeFromLeft(10);
    cancelUI->setBounds(hr.removeFromLeft(100));
}

void SimulationUI::timerCallback()
{
    if (!shouldRepaint)
        return;

    repaint();
    shouldRepaint = false;
}

bool SimulationUI::keyPressed(const KeyPress &e)
{
    if (e.getKeyCode() == KeyPress::spaceKey)
    {
        if (simul->isThreadRunning())
            simul->cancelTrigger->trigger();
        else
        {
            entityHistory.clear();

            int nbEnt = 7;
            simul->startTrigger->trigger();
        }
    }

    return false;
}

void SimulationUI::newStep(Simulation *)
{

    Array<float> entityValues;
    for (auto &ent : Simulation::getInstance()->entities)
    {
        entityValues.add(ent->concent);
        entityRefs.addIfNotAlreadyThere(ent);
    }
    entityHistory.add(entityValues);

    shouldRepaint = true;
}

void SimulationUI::simulationStarted(Simulation *)
{
    entityHistory.clear();
    entityRefs.clear();
    //pour commencer le graphe avant de faire le premier pas. Fait crasher.
    Array<float> entityValues;
    for (auto &ent : Simulation::getInstance()->entities)
    {
        entityValues.add(ent->concent);
        entityRefs.addIfNotAlreadyThere(ent);
    }
    entityHistory.add(entityValues);

}

void SimulationUI::simulationFinished(Simulation *)
{
}