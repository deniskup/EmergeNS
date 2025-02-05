#include "PACUI.h"

PACUI::PACUI() : ShapeShifterContentComponent("RACs"),
                 simul(Simulation::getInstance())
{
    
    oneColorToggle.reset(simul->oneColor->createToggle());
    //oneColorToggle->setSize(50, 20);
    addAndMakeVisible(oneColorToggle.get());
    oneColorToggle->setVisible(false);
    

    simul->addAsyncSimulationListener(this);
    simul->addAsyncContainerListener(this);
    startTimerHz(20);
  
}

PACUI::~PACUI()
{
    simul->removeAsyncSimulationListener(this);
    simul->removeAsyncContainerListener(this);
}

void PACUI::paint(juce::Graphics &g)
{
    PACsBounds = getLocalBounds();
    g.fillAll(Colours::black);
    g.setColour(Colours::white);
    g.setFont(14.0f);
   float width = PACsBounds.getWidth() - rightMargin;
    float height = PACsBounds.getHeight();

    // create a RACsHistory with only the PAC the become RACs
    Array<int> RACid;
    for (int j = 0; j < PACsHistory[0].size(); ++j)
        {
            if (RACList[j])
            {
                RACid.add(j);
            }
        }

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

    // declare function distort
    auto distort = [](float val) -> float
    {
        if (val < .1)
        {
            return val * 5;
        }
        else
        {
            return (.5 * val + .4) / .9;
        }
    };


    // do a colour logarithmic scale, say up to 10^-5
    Array<Colour>
        colours({Colours::white, Colours::yellow, Colours::orange, Colours::red, Colours::magenta, Colours::blue, Colours::green});

    // draw the logarithmic scale on the top
    float yTop = .05 * height;
    float xLegend = .1 * width;

    float xButton = .1 * width;

    //put the button
    oneColorToggle->setVisible(true);
    oneColorToggle->setBounds(width-xButton*.95, yTop*.1, xButton*.9, yTop*.8);

    // write the legend
    g.drawText(" Log Scale:", 0, 0, xLegend, yTop, Justification::left, true);
    int gradient = 50;
    float xColourStep = (width - xLegend-xButton) / (colours.size() * gradient);
    for (int i = 0; i < colours.size(); ++i)
    {
        for (int j = 0; j < gradient; ++j)
        {
            g.setColour(colours[colours.size() - i - 1].withAlpha(distort(j * 1.f / gradient)));
            g.fillRect(xLegend + (gradient * i + j) * xColourStep, 0.f, xColourStep, yTop * .9);
        }
    }

    // for indexes of RACS
    float xLeft = leftMargin;

  
    // steps for drawing the RACs
    float xScale = (width - xLeft) / RACsHistory.size();
    float yScale = (height - yTop) / RACsHistory[0].size();

    // at the left column, display the RACs identifiers
    g.setColour(Colours::white);
    g.setOpacity(.8f);
    g.setFont(14.0f);
    for (int j = 0; j < RACsHistory[0].size(); ++j)
    {
        g.drawText(to_string(RACid[j] + 1), 0.f, yTop + j * yScale, xLeft, yScale, Justification::centred, true);
    }

    // draw vertical line after indexes
    g.drawLine(xLeft, yTop, xLeft, height - yTop * .9, .8f);
    //draw vertical line at the end
    g.drawLine(width, yTop, width, height - yTop * .9, .8f);
    // draw horizontal line at yTop
    g.drawLine(0, yTop * .9, width, yTop * .9, .8f);

    // todo draw with colours
    //  use maxRACs to affect colours to each RAC
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
    int coef = 1;
    for (int i = 0; i < colours.size(); i++)
    {
        coefs.add(coef);
        coef *= 10;
    }

    for (int i = 0; i < RACsHistory.size(); ++i)
    {
        for (int j = 0; j < RACsHistory[i].size(); ++j)
        {
            float xCoord = xLeft + i * xScale;
            float yCoord = yTop + j * yScale;
            
            // draw vertical line if RACS was previously off            
            // g.setOpacity(1.f);
            // g.setColour(Colours::lightgreen);
            // if (i > 0 && RACsHistory[i - 1][j] == 0. && RACsHistory[i][j] > 0.)
            // {
            //     g.drawLine(xCoord, yCoord, xCoord, yCoord + yScale * .9, 1.f);
            // }

            float valToMax;
            int colIndex;
            // display parameter, one color per RAC
            if (simul->oneColor->boolValue())
            {
                // to display only one color per RAC
                valToMax = RACsHistory[i][j] * coefs[RACindex[j]] / maxPAC;
                colIndex = RACindex[j];
            }
            else
            {
                // to display only depending on local value
                valToMax = RACsHistory[i][j] / maxPAC;
                colIndex = 0;

                while (valToMax < 0.1 && colIndex < colours.size() - 1)
                {
                    valToMax *= 10;
                    colIndex++;
                }
            }

            g.setColour(colours[colIndex].withAlpha(distort(valToMax)));
            g.fillRect(xCoord, yCoord, xScale, yScale * .9);
        }
    }


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

void PACUI::newMessage(const ContainerAsyncEvent &e)
{
    if (e.type == ContainerAsyncEvent::EventType::ControllableFeedbackUpdate)
    {
        if (e.targetControllable == simul->oneColor)
        {
            repaint();
        }
    }
}
