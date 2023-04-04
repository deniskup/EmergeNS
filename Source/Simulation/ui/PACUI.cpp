#include "PACUI.h"

PACUI::PACUI() : ShapeShifterContentComponent("PACs"),
                 simul(Simulation::getInstance())
{
    simul->addAsyncSimulationListener(this);
    startTimerHz(20);
}

PACUI::~PACUI()
{
    simul->removeAsyncSimulationListener(this);
}

void PACUI::paint(juce::Graphics &g)
{
    PACsBounds = getLocalBounds();
    g.fillAll(Colours::black);
    g.setColour(Colours::white);
    g.setFont(14.0f);
    float width = PACsBounds.getWidth();
    float height = PACsBounds.getHeight();

    if (PACsHistory.size() == 0)
        return;

    maxPAC = PACsHistory[0][0]; // initialization

    for (int i = 0; i < PACsHistory.size(); ++i)
    {
        for (int j = 0; j < PACsHistory[i].size(); ++j)
        {
            maxPAC = jmax(maxPAC, PACsHistory[i][j]);
        }
    }
    if (maxPAC == 0.0f)
        maxPAC = 1.0f; // safety
    float xScale = width / PACsHistory.size();
    float yScale = height / PACsHistory[0].size();

    cout << "maxPAC:" << maxPAC << endl;

    for (int i = 0; i < PACsHistory.size(); ++i)
    {
        for (int j = 0; j < PACsHistory[i].size(); ++j)
        {
                g.setColour(Colours::white.withAlpha(PACsHistory[i][j] / maxPAC));
                g.fillRect(i * xScale, j * yScale, xScale, yScale*.9);
        }
    }

    // g.drawText("PACs", PACsBounds, Justification::centred, true);
}

void PACUI::resized()
{
}

void PACUI::timerCallback()
{
    if (shouldRepaint)
    {
        repaint();
        shouldRepaint = false;
    }
}

void PACUI::newMessage(const Simulation::SimulationEvent &ev)
{
    switch (ev.type)
    {
    case Simulation::SimulationEvent::UPDATEPARAMS:
    {
        shouldRepaint = true;
    }
    case Simulation::SimulationEvent::WILL_START:
    {

        PACsHistory.clear();
        repaint();
    }
    break;

    case Simulation::SimulationEvent::STARTED:
    {
        // PACsHistory.add(ev.PACsValues);
    }
    break;

    case Simulation::SimulationEvent::NEWSTEP:
    {
        PACsHistory.add(ev.PACsValues);
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
