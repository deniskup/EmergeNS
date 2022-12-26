
#include "SimulationUI.h"

SimulationUI::SimulationUI() : ShapeShifterContentComponent(Simulation::getInstance()->niceName),
                               simul(Simulation::getInstance())
{
    // maxStepsUI.reset(simul->maxSteps->createStepper());
    dtUI.reset(simul->dt->createLabelParameter());
    dtUI->setSuffix(" s");
    totalTimeUI.reset(simul->totalTime->createLabelParameter());
    totalTimeUI->setSuffix(" s");
    curStepUI.reset(simul->curStep->createSlider());
    startUI.reset(simul->startTrigger->createButtonUI());
    cancelUI.reset(simul->cancelTrigger->createButtonUI());

    addAndMakeVisible(dtUI.get());
    addAndMakeVisible(totalTimeUI.get());
    addAndMakeVisible(curStepUI.get());
    addAndMakeVisible(startUI.get());
    addAndMakeVisible(cancelUI.get());

    // curStepUI->customLabel = "Progress";

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

    Rectangle<int> r = getLocalBounds().withTop(60);

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
    g.drawRoundedRectangle(r.toFloat(), 8, 1.f);

    if (!entityHistory.isEmpty())
    {
        float stepX = 1.0f / jmax(simul->maxSteps->intValue(), 1);
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
            g.setColour(entityRefs[i]->color.brighter(.3f).withSaturation(1));
            g.strokePath(*paths[i], PathStrokeType(1.2));
        }
    }
}

void SimulationUI::resized()
{
    Rectangle<int> r = getLocalBounds();
    Rectangle<int> hr = r.removeFromTop(27).reduced(2);
    // maxStepsUI->setBounds(hr.removeFromLeft(200));
    hr=hr.withSizeKeepingCentre(330,25);
    dtUI->setBounds(hr.removeFromLeft(100));
    // hr.removeFromLeft(30);
    totalTimeUI->setBounds(hr.removeFromLeft(200));
    r.removeFromTop(10);
    hr = r.removeFromTop(25);
    hr= hr.withSizeKeepingCentre(420,25);
    startUI->setBounds(hr.removeFromLeft(100));
    hr.removeFromLeft(30);
    cancelUI->setBounds(hr.removeFromLeft(100));
    hr.removeFromLeft(40);
    curStepUI->setBounds(hr.removeFromLeft(150));
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

void SimulationUI::simulationWillStart(Simulation *)
{
    entityHistory.clear();
    entityRefs.clear();
}

void SimulationUI::simulationStarted(Simulation *)
{
    // pour commencer le graphe avant de faire le premier pas. Fait crasher.
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
    shouldRepaint = true;
}