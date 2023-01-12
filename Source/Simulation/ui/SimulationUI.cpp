
#include "SimulationUI.h"

SimulationUI::SimulationUI() : ShapeShifterContentComponent(Simulation::getInstance()->niceName),
                               simul(Simulation::getInstance())
{
    // maxStepsUI.reset(simul->maxSteps->createStepper());
    dtUI.reset(simul->dt->createLabelParameter());
    dtUI->setSuffix(" s");
    totalTimeUI.reset(simul->totalTime->createLabelParameter());
    totalTimeUI->setSuffix(" s");
    perCentUI.reset(simul->perCent->createSlider());
    perCentUI->suffix = "%";
    maxConcentUI.reset(simul->maxConcent->createLabelParameter());
    startUI.reset(simul->startTrigger->createButtonUI());
    cancelUI.reset(simul->cancelTrigger->createButtonUI());
    generatedUI.reset(simul->generated->createToggle());

    // local parameter, won't be saved in the file.
    // maxC.reset(new FloatParameter("MaxC","descr",5.f,0));
    // maxCUI.reset(maxC->createLabelParameter())

    addAndMakeVisible(dtUI.get());
    addAndMakeVisible(totalTimeUI.get());
    addAndMakeVisible(maxConcentUI.get());
    addAndMakeVisible(startUI.get());
    addAndMakeVisible(cancelUI.get());
    addAndMakeVisible(generatedUI.get());
    addAndMakeVisible(perCentUI.get());

    perCentUI->customLabel = "Progress";

    startTimerHz(20);
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

    Rectangle<int> r = getLocalBounds().withTop(100);

    g.setFont(12);

    r.reduce(10, 10);
    g.setColour(Colours::white.withAlpha(simul->isThreadRunning() ? .1f : .005f));
    g.fillRoundedRectangle(r.toFloat(), 8);
    g.setColour(Colours::white.withAlpha(.3f));
    g.drawRoundedRectangle(r.toFloat(), 8, 1.f);

    if (toClear)
    {
        toClear = false;
        // DBG("cleared");
        return;
    }
    if (simul->isThreadRunning() && !simul->realTime->boolValue()) // si option realTime
        return;
    if (entityHistory.isEmpty())
        return;

    float stepX = 1.0f / jmax(simul->maxSteps->intValue(), 1);
    // float maxConcent = 5;
    OwnedArray<Path> paths;
    for (auto &e : entityHistory[0])
    {
        Path *p = new Path();
        Point<float> ep = r.getRelativePoint(0.f, 1 - e / simul->maxConcent->floatValue()).toFloat();
        p->startNewSubPath(ep);
        paths.add(p); // add one path per entity
    }

    for (int i = 1; i < entityHistory.size(); i++)
    {
        Array<float> values = entityHistory[i];
        for (int j = 0; j < values.size(); j++)
        {
            if (values[j] > simul->maxConcent->floatValue())
                continue;
            // TODO avoid ugly horizontal line if curve goes out and back in.
            Point<float> ep = r.getRelativePoint(i * stepX, 1 - values[j] / simul->maxConcent->floatValue()).toFloat();
            // g.drawEllipse(Rectangle<float>(10,10).withCentre(ep), 2.f);
            paths[j]->lineTo(ep);
        }
    }
    jassert(entityRefs.size() >= paths.size());
    for (int i = 0; i < paths.size(); i++)
    {
        g.setColour(entityRefs[i]->color); // g.setColour(entityRefs[i]->color.brighter(.3f).withSaturation(1));
        g.strokePath(*paths[i], PathStrokeType(1.2));
    }
}

void SimulationUI::resized()
{
    Rectangle<int> r = getLocalBounds();
    Rectangle<int> hr = r.removeFromTop(27).reduced(2);
    // maxStepsUI->setBounds(hr.removeFromLeft(200));
    hr = hr.withSizeKeepingCentre(500, 25);
    dtUI->setBounds(hr.removeFromLeft(100));
    hr.removeFromLeft(20);
    totalTimeUI->setBounds(hr.removeFromLeft(200));
    generatedUI->setBounds(hr.removeFromRight(100));
    r.removeFromTop(10);
    hr = r.removeFromTop(25);
    hr = hr.withSizeKeepingCentre(420, 25);
    startUI->setBounds(hr.removeFromLeft(100));
    hr.removeFromLeft(30);
    cancelUI->setBounds(hr.removeFromLeft(100));
    hr.removeFromLeft(40);
    maxConcentUI->setBounds(hr.removeFromLeft(150));
    r.removeFromTop(5);
    perCentUI->setBounds(r.removeFromTop(25).reduced(4));
}

void SimulationUI::timerCallback()
{
    if (shouldRepaint)
    {
        repaint();
        shouldRepaint = false;
    }
    if (toClear)
    {
        // DBG("clear call");
        repaint();
    }
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
            entityRefs.clear();
            simul->startTrigger->trigger();
        }
    }

    return false;
}

void SimulationUI::newStep(Simulation *)
{

    Array<float> entityValues;
    for (auto &ent : entityRefs)
    {
        entityValues.add(ent->concent);
    }

    entityHistory.add(entityValues);

    shouldRepaint = true; // seul qui marche pour l'instant
    // shouldRepaint = simul->realTime->boolValue(); //ce qu'on voudrait pour gagner du temps
}

void SimulationUI::simulationWillStart(Simulation *)
{
    entityHistory.clear();
    entityRefs.clear();
    // DBG("to clear");
    toClear = true;
}

void SimulationUI::simulationStarted(Simulation *)
{
    Array<float> entityValues;
    for (auto &ent : Simulation::getInstance()->entities)
    {
        if (ent->draw)
        {
            entityValues.add(ent->concent);
            entityRefs.addIfNotAlreadyThere(ent);
        }
    }
    entityHistory.add(entityValues);
}

void SimulationUI::simulationFinished(Simulation *)
{
    shouldRepaint = true;
    // DBG("history of size "<<entityHistory.size());
    // DBG("entityrefs of size "<<entityRefs.size());
}