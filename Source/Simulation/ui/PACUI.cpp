#include "PACUI.h"

PACUI::PACUI() : ShapeShifterContentComponent("RACs"),
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

    // create a RACsHistory with only the PAC the become RACs

    Array<Array<float>> RACsHistory;
    for (int i = 0; i < PACsHistory.size(); ++i)
    {
        Array<float> RACs;
        for (int j = 0; j < PACsHistory[i].size(); ++j)
        {
            if (RACList[j])
            {
                RACs.add(PACsHistory[i][j]);
            }
        }
        RACsHistory.add(RACs);
    }

    if (RACsHistory.size() == 0)
        return;

    float maxPAC = 0.0f;

    // find the max PAC and for each RAC compute its max value

    Array<float> maxRACs;
    for (int j = 0; j < RACsHistory[0].size(); ++j)
    {
        maxRACs.add(0.0f);
    }

    for (int i = 0; i < RACsHistory.size(); ++i)
    {
        for (int j = 0; j < RACsHistory[i].size(); ++j)
        {
            maxPAC = jmax(maxPAC, RACsHistory[i][j]);
            maxRACs.set(j, jmax(maxRACs[j], RACsHistory[i][j]));
        }
    }
    if (maxPAC == 0.0f)
        maxPAC = 1.0f; // safety



    // do a colour logarithmic scale, say up to 10^-5
    Array<Colour> colours({Colours::white, Colours::yellow, Colours::orange, Colours::red, Colours::magenta, Colours::blue, Colours::green});

    // draw the logarithmic scale on the top
    float yTop = .05 * height;
    float xLegend = .1 * width;
    // write the legend
    g.drawText(" Log Scale:", 0, 0, xLegend, yTop, Justification::left, true);
    int degradation = 30;
    float xColourStep = (width -xLegend) / (colours.size() * degradation);
    for (int i = 0; i < colours.size(); ++i)
    {
        for (int j = 0; j < degradation; ++j)
        {
            g.setColour(colours[colours.size()-i-1].withAlpha(j * 1.f / degradation));
            g.fillRect(xLegend+(degradation * i + j) * xColourStep, 0.f, xColourStep, yTop * .9);
        }
    }

    //for indexes of RACS
    float xLeft = .02 * width;

    // steps for drawing the RACs
    float xScale = (width - xLeft) / RACsHistory.size();
    float yScale = (height - yTop) / RACsHistory[0].size();

    // at the left column, display the RACs identifiers
    g.setColour(Colours::white);
    g.setOpacity(.8f);
    g.setFont(14.0f);
    for (int j = 0; j < RACsHistory[0].size(); ++j)
    {
        g.drawText(to_string(j + 1), 0.f, yTop + j * yScale, xLeft, yScale, Justification::centred, true);
    }

    // draw vertical line after indexes
    g.drawLine(xLeft, yTop, xLeft, height - yTop*.9, .8f);
    //draw horizontal line at yTop
    g.drawLine(0, yTop*.9, width, yTop*.9, .8f);


    // use maxRACs to affect colours to each RAC
    Array<int> RACindex;
    for (int j = 0; j < RACsHistory[0].size(); ++j)
    {
        float valRAC = maxRACs[j] / maxPAC;
        int colIndex = 0;
        while (valRAC < 0.1 && colIndex < colours.size() - 1)
        {
            valRAC *= 10;
            colIndex++;
        }
        RACindex.add(colIndex);
    }
    Array<float> coefs;
    int coef=1;
    for(int i=0;i<colours.size();i++)
    {
        coefs.add(coef);
        coef*=10;
    }

    for (int i = 0; i < RACsHistory.size(); ++i)
    {
        for (int j = 0; j < RACsHistory[i].size(); ++j)
        {
            float valToMax = RACsHistory[i][j] *coefs[RACindex[j]] / maxPAC;
            
            //scaling:valToMax 0 -> alpha 0, but .1 -> alpha.5 and 1 -> alpha 1 via two linear functions
            float alpha;
            if(valToMax<.1)
            {
                alpha=valToMax*5;
            }
            else
            {
                alpha=(.5*valToMax+.4)/.9;
            }

            g.setColour(colours[RACindex[j]].withAlpha(alpha));
            g.fillRect(xLeft + i * xScale, yTop + j * yScale, xScale, yScale * .9);
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
        RACList = ev.RACList;
        // shouldRepaint=simul->realTime->boolValue())
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
