
#include "SimulationUI.h"

SimulationUI::SimulationUI() : ShapeShifterContentComponent(Simulation::getInstance()->niceName),
                               simul(Simulation::getInstance())
                               //uiStep(1)
{

    dtUI.reset(simul->dt->createLabelParameter());
    dtUI->setSuffix(" s");
    totalTimeUI.reset(simul->totalTime->createLabelParameter());
    totalTimeUI->setSuffix(" s");
    pointsDrawnUI.reset(simul->pointsDrawn->createLabelUI());
    perCentUI.reset(simul->perCent->createSlider());
    perCentUI->suffix = "%";
    maxConcentUI.reset(simul->maxConcent->createLabelParameter());
    genUI.reset(simul->genTrigger->createButtonUI());
    startUI.reset(simul->startTrigger->createButtonUI());
    genstartUI.reset(simul->genstartTrigger->createButtonUI());
    cancelUI.reset(simul->cancelTrigger->createButtonUI());
    generatedUI.reset(simul->generated->createToggle());
    autoScaleUI.reset(simul->autoScale->createToggle());

    // local parameter, won't be saved in the file.
    // maxC.reset(new FloatParameter("MaxC","descr",5.f,0));
    // maxCUI.reset(maxC->createLabelParameter())

    dtUI->setSize(100, 20);
    totalTimeUI->setSize(200, 20);
    perCentUI->setSize(100, 20);
    maxConcentUI->setSize(150, 20);
    genUI->setSize(100, 20);
    startUI->setSize(100, 20);
    genstartUI->setSize(100, 20);
    cancelUI->setSize(100, 20);
    generatedUI->setSize(100, 20);
    autoScaleUI->setSize(100, 20);
    pointsDrawnUI->setSize(150, 20);

    addAndMakeVisible(dtUI.get());
    addAndMakeVisible(totalTimeUI.get());
    addAndMakeVisible(maxConcentUI.get());
    addAndMakeVisible(genUI.get());
    addAndMakeVisible(startUI.get());
    addAndMakeVisible(genstartUI.get());
    addAndMakeVisible(cancelUI.get());
    addAndMakeVisible(autoScaleUI.get());
    addAndMakeVisible(generatedUI.get());
    addAndMakeVisible(perCentUI.get());
    addAndMakeVisible(pointsDrawnUI.get());

    maxConcentUI->setVisible(!simul->autoScale->boolValue());
    perCentUI->customLabel = "Progress";

    simBounds.setSize(500, 500);

    startTimerHz(20);
    simul->addAsyncSimulationListener(this);
    simul->addAsyncContainerListener(this);
}

SimulationUI::~SimulationUI()
{
    simul->removeAsyncSimulationListener(this);
    simul->removeAsyncContainerListener(this);
}

//==============================================================================
void SimulationUI::paint(juce::Graphics &g)
{
    float maxC = simul->autoScale->boolValue() ? simul->recordDrawn : simul->maxConcent->floatValue();
    // (Our component is opaque, so we must completely fill the background with a solid colour)
    g.fillAll(BG_COLOR);
    
    simBounds = getLocalBounds().withTop(100).withTrimmedBottom(100).reduced(10);

    //g.setFont(12);
    g.setColour(NORMAL_COLOR);
    g.drawRoundedRectangle(simBounds.toFloat(), 4, 3.f);
    g.setColour(Colours::white.withAlpha(simul->isThreadRunning() ? .1f : .005f));
    g.fillRoundedRectangle(simBounds.toFloat(), 4);

    g.setColour (Colours::white);
    g.setFont (14);
    Rectangle<int> botBounds= getLocalBounds().removeFromBottom(50);
    string read="Parameters Generated";
    if(!simul->ready) read="Not ready";
    g.drawText(read, botBounds, Justification::centred);
    
    //if simulation generated
    //if(simul->generated->boolValue())

    //TODO rectangle bottom left



    //if simulation finished
    //TODO rectangle bottom right

    
    if (simul->isThreadRunning() && !simul->realTime->boolValue()) // si pas option realTime
        return;
    if (entityHistory.isEmpty())
        return;

    


    float stepX = 1.0f / jmax(entityHistory.size() - 1, 1);
    // float maxConcent = 5;
    OwnedArray<Path> paths;
    for (auto &e : entityHistory[0])
    {
        float v = 1 - e / maxC;
        v = jmax(v, 0.f);

        Path *p = new Path();
        Point<float> ep = simBounds.getRelativePoint(0.f, v).toFloat();
        p->startNewSubPath(ep);
        paths.add(p); // add one path per entity
    }

    for (int i = 1; i < entityHistory.size(); i++)
    {
        Array<float> values = entityHistory[i];
        for (int j = 0; j < values.size(); j++)
        {
            float v = 1 - values[j] / maxC;
            v = jmax(v, 0.f);
            Point<float> ep = simBounds.getRelativePoint(i * stepX, v).toFloat();
            // g.drawEllipse(Rectangle<float>(10,10).withCentre(ep), 2.f);
            // optimisation possible: ne pas rajouter si c'est le meme x
            paths[j]->lineTo(ep);
        }
    }
    jassert(entityColors.size() >= paths.size());
    for (int i = 0; i < paths.size(); i++)
    {
        g.setColour(entityColors[i]);
        g.strokePath(*paths[i], PathStrokeType(1.2));
    }

    g.setColour(BG_COLOR);
    g.drawRect(simBounds.toFloat(), 1);
    g.setColour(NORMAL_COLOR);
    g.drawRoundedRectangle(simBounds.toFloat(), 4, 3.f);
}

void SimulationUI::resized()
{
    Rectangle<int> r = getLocalBounds();
    Rectangle<int> hr = r.removeFromTop(27);

    int width1 = dtUI->getWidth() + 20 + totalTimeUI->getWidth() + 20+ pointsDrawnUI->getWidth()+ 40 + generatedUI->getWidth();

    hr.reduce((hr.getWidth() - width1) / 2, 0);

    dtUI->setBounds(hr.removeFromLeft(dtUI->getWidth()));
    hr.removeFromLeft(20);
    totalTimeUI->setBounds(hr.removeFromLeft(totalTimeUI->getWidth()));
    hr.removeFromLeft(20);
    pointsDrawnUI->setBounds(hr.removeFromLeft(pointsDrawnUI->getWidth()));
    hr.removeFromLeft(40);
    generatedUI->setBounds(hr.removeFromRight(generatedUI->getWidth()));

    r.removeFromTop(8);
    hr = r.removeFromTop(30);

    int width2 = genUI->getWidth() + 20 + startUI->getWidth() + 20 + genstartUI->getWidth() + 20 + cancelUI->getWidth() + 50 + autoScaleUI->getWidth() + 10 + maxConcentUI->getWidth();
    hr.reduce((hr.getWidth() - width2) / 2, 0);

    genUI->setBounds(hr.removeFromLeft(genUI->getWidth()));
    hr.removeFromLeft(20);

    startUI->setBounds(hr.removeFromLeft(startUI->getWidth()));
    hr.removeFromLeft(20);

    genstartUI->setBounds(hr.removeFromLeft(genstartUI->getWidth()));
    hr.removeFromLeft(20);

    cancelUI->setBounds(hr.removeFromLeft(cancelUI->getWidth()));
    hr.removeFromLeft(50);
    autoScaleUI->setBounds(hr.removeFromLeft(autoScaleUI->getWidth()));
    hr.removeFromLeft(10);
    maxConcentUI->setBounds(hr.removeFromLeft(maxConcentUI->getWidth()));

    r.removeFromTop(8);
    perCentUI->setBounds(r.removeFromTop(25).reduced(4));



}

void SimulationUI::timerCallback()
{
    if (shouldRepaint)
    {
        repaint();
        shouldRepaint = false;
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
            entityColors.clear();
            simul->startTrigger->trigger();
        }
    }

    return false;
}

void SimulationUI::newMessage(const Simulation::SimulationEvent &ev)
{
    switch (ev.type)
    {
     case Simulation::SimulationEvent::UPDATEPARAMS:
    {
        shouldRepaint = true;
    }
    case Simulation::SimulationEvent::WILL_START:
    {
        // int maxPoints = simBounds.getWidth();
        entityHistory.clear();
        entityColors.clear();
        // uiStep = jmax(1, (int)(simul->maxSteps / maxPoints));
        // resolution decided by ui
        repaint();
    }
    break;

    case Simulation::SimulationEvent::STARTED:
    {
        entityColors = ev.entityColors;
        entityHistory.add(ev.entityValues);
    }
    break;

    case Simulation::SimulationEvent::NEWSTEP:
    {
        // if (ev.curStep % uiStep == 0)
        entityHistory.add(ev.entityValues);
        //print for debug
     //   NLOG("Value", ev.entityValues[0]);

        if (simul->realTime->boolValue())
            shouldRepaint = true;
    }
    break;

    case Simulation::SimulationEvent::FINISHED:
    {
        resized();
        repaint();
    }
    break;
    }
}

void SimulationUI::newMessage(const ContainerAsyncEvent &e)
{
    if (e.type == ContainerAsyncEvent::EventType::ControllableFeedbackUpdate)
    {
        if (e.targetControllable == simul->autoScale)
        {
            maxConcentUI->setVisible(!simul->autoScale->boolValue());
            repaint();
        }
        else if (e.targetControllable == simul->maxConcent)
        {
            shouldRepaint = true;
        }
    }
}
