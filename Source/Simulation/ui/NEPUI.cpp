#include "NEPUI.h"

using namespace juce;


NEPUI::NEPUI() : ShapeShifterContentComponent(NEP::getInstance()->niceName),
                               nep(NEP::getInstance())
{
  
    editorUI.reset(new GenericControllableContainerEditor(nep, true));
    addAndMakeVisible(editorUI.get());
  
    // set view component 
    addAndMakeVisible(vp);
    vp.setScrollBarsShown(true, true);
    vp.setScrollBarThickness(10);
    vp.setBounds(getLocalBounds());
    vp.setViewedComponent(editorUI.get(), false);
  
  nep->addAsyncNEPListener(this);
  nep->addAsyncContainerListener(this);
  

  
}

NEPUI::~NEPUI()
{
  nep->removeAsyncNEPListener(this);
  nep->removeAsyncContainerListener(this);

}

// #HERE
// tick marks as well as labels do not display correctly in UI
void NEPUI::paintAxis(
    juce::Graphics& g,
    juce::Rectangle<int> r,
    String type,
    int nticks,
    float min,
    float max,
    int ndigits,
    String scale)
{
    if (nticks <= 0 || min >= max)
        return;

    const bool logScale = (scale == "log");

    // Logarithmic axes require positive bounds.
    if (logScale && (min <= 0.0f || max <= 0.0f))
        return;

    g.setColour(NORMAL_COLOR);
    g.setFont(10.0f);

    const int markwidth = 4;
    const int markheight = 2;
    const int textboxwidth = 45;
    const int textboxheight = 15;

    const int shiftXaxisLabels = 10;
    const int shiftYaxisLabels = 25;

    const double logMin = logScale ? std::log10(min) : 0.0;
    const double logMax = logScale ? std::log10(max) : 0.0;

    for (int i = 0; i <= nticks; ++i)
    {
        const double fraction = static_cast<double>(i) / nticks;

        int markX;
        int markY;

        // Draw tick marks, excluding the endpoints.
        if (i > 0 && i < nticks)
        {
            if (type == "X")
            {
                markX = r.getX()
                    + static_cast<int>(std::round(r.getWidth() * fraction));

                markY = r.getBottom();

                juce::Rectangle<int> m(
                    markX,
                    markY - markwidth / 2,
                    markheight,
                    markwidth);

                g.drawRect(m, markheight);
            }
            else
            {
                markX = r.getX();

                markY = r.getY()
                    + static_cast<int>(std::round(r.getHeight() * fraction));

                juce::Rectangle<int> m(
                    markX - markwidth / 2,
                    markY,
                    markwidth,
                    markheight);

                g.drawRect(m, markheight);
            }
        }

        // Draw tick labels.
        if (type == "X")
        {
            juce::String label;

            // Display only the first and last labels.
            if (i == 0)
                label = juce::String(min, ndigits);

            if (i == nticks)
                label = juce::String(max, ndigits);

            const int labelX = r.getX()
                + static_cast<int>(std::round(r.getWidth() * fraction))
                - textboxwidth / 2;

            const int labelY = r.getBottom() + shiftXaxisLabels;

            juce::Rectangle<int> labelpos(
                labelX, labelY, textboxwidth, textboxheight);

            if (i == 0 || i == nticks)
            {
                g.drawText(
                    label,
                    labelpos,
                    juce::Justification::centred,
                    true);
            }
        }
        else if (type == "Y")
        {
            // Position from the bottom towards the top.
            const double axisFraction = 1.0 - fraction;

            const int labelX = r.getX() - shiftYaxisLabels;

            const int labelY = r.getY()
                + static_cast<int>(
                    std::round(r.getHeight() * axisFraction))
                - textboxheight / 2;

            juce::Rectangle<int> labelpos(
                labelX, labelY, textboxwidth, textboxheight);

            double value;

            if (logScale)
            {
                // Interpolate in log-space, then return to linear values.
                value = std::pow(
                    10.0,
                    logMin + fraction * (logMax - logMin));
            }
            else
            {
                // Linear interpolation.
                value = min + fraction * (max - min);
            }

            juce::String label(value, ndigits);

            g.drawText(
                label,
                labelpos,
                juce::Justification::centred,
                true);
        }
    }
}

void NEPUI::paintOneMonitoredQuantity(
    juce::Graphics& g,
    juce::Rectangle<int> r,
    String title,
    Array<double> data,
    String scale = "linear")
{
    if (data.isEmpty())
        return;

    if (title != "H")
    {
      jassert(data.size() == iterations.size());

      if (iterations.isEmpty() || data.size() != iterations.size())
        return;
    }

    const bool logScale = (scale == "log");

    // Une échelle logarithmique nécessite des valeurs strictement positives.
    if (logScale)
    {
        for (double value : data)
        {
            if (!std::isfinite(value) || value <= 0.0)
            {
                DBG("Cannot use logarithmic scale for " + title
                    + ": data must be strictly positive and finite.");
                return;
            }
        }
    }

    // Draw the box.
    g.setColour(NORMAL_COLOR);
    g.drawRoundedRectangle(r.toFloat(), 4, 2.0f);

    // Find the bounds.
    double minX = *std::min_element(iterations.begin(), iterations.end());
    double maxX = *std::max_element(iterations.begin(), iterations.end());

    double minY = *std::min_element(data.begin(), data.end());
    double maxY = *std::max_element(data.begin(), data.end());

    if (!std::isfinite(minX) || !std::isfinite(maxX))
        return;

    if (minX == maxX)
    {
        const double margin = std::max(1.0, std::abs(minX) * 0.05);
        minX -= margin;
        maxX += margin;
    }

    if (logScale)
    {
        // Work in log10-space.
        double logMinY = std::log10(minY);
        double logMaxY = std::log10(maxY);

        // Avoid a zero range when all values are identical.
        if (logMinY == logMaxY)
        {
            logMinY -= 0.5;
            logMaxY += 0.5;
        }

        // Add 5% margin in logarithmic space.
        const double margin = 0.05 * (logMaxY - logMinY);
        logMinY -= margin;
        logMaxY += margin;

        minY = std::pow(10.0, logMinY);
        maxY = std::pow(10.0, logMaxY);
    }
    else
    {
        // Linear scale: preserve the existing behaviour.
        double rangeY = maxY - minY;

        if (rangeY == 0.0)
        {
            const double margin = std::max(1.0, std::abs(maxY) * 0.05);
            minY -= margin;
            maxY += margin;
        }
        else
        {
            maxY += 0.05 * rangeY;

            if (title == "Action")
                minY -= 0.05 * rangeY;
        }
    }

    const double rangeY = logScale
        ? std::log10(maxY) - std::log10(minY)
        : maxY - minY;

    const double rangeX = maxX - minX;

    if (rangeX <= 0.0 || rangeY <= 0.0)
        return;

    // Convert data coordinates to pixel coordinates.
    auto toPixel = [&](double x, double y) -> juce::Point<float>
    {
        const double normX = (x - minX) / rangeX;

        const double normY = logScale
            ? (std::log10(y) - std::log10(minY)) / rangeY
            : (y - minY) / rangeY;

        const float pixelX =
            static_cast<float>(r.getX() + normX * r.getWidth());

        const float pixelY =
            static_cast<float>(r.getBottom() - normY * r.getHeight());

        return { pixelX, pixelY };
    };

    // Build the path.
    juce::Path path;

    path.startNewSubPath(
        toPixel(iterations.getUnchecked(0), data.getUnchecked(0)));

    for (int k = 1; k < data.size(); ++k)
    {
        path.lineTo(
            toPixel(iterations.getUnchecked(k), data.getUnchecked(k)));
    }

    // Draw the data.
    juce::Colour col = juce::Colours::purple;

    if (title == "Action")
        col = juce::Colours::yellow;
    else if (title == "Cutoff frequency" || title == "Convergence")
        col = juce::Colours::pink;
    else if (title == "nPoints")
        col = juce::Colours::powderblue;
    else if (title == "Metric")
        col = juce::Colours::orangered;
    else if (title == "H")
    {
      col = juce::Colours::orangered;
      scale = "log";
    }

    g.setColour(col);
    g.strokePath(path, juce::PathStrokeType(1.2f));

    // Draw the axes.
    const int nticksX = 4;
    const int nticksY = 4;

    const int ndigitsX = 0;
    const int ndigitsY = (title == "nPoints") ? 0 : 2;

    paintAxis(g, r, "X", nticksX,
              static_cast<float>(minX),
              static_cast<float>(maxX),
              ndigitsX, "linear");

    paintAxis(g, r, "Y", nticksY,
              static_cast<float>(minY),
              static_cast<float>(maxY),
              ndigitsY, scale);

    // Draw the title.
    g.setFont(15.0f);

    const int titleboxwidth = 150;
    const int titleX = r.getX() + r.getWidth() / 2 - titleboxwidth / 2;
    const int titleY = r.getY() - 20;

    juce::Rectangle<int> titlepos(titleX, titleY, titleboxwidth, 20);
    g.drawText(title, titlepos, juce::Justification::centred, true);
}



void NEPUI::paint(juce::Graphics & g)
{
  
  //if (nep->state != NEP::NEPState::Descending)
   // return;
    
  if (iterations.size()==0)
    return;
  
  /*
  cout << "calling paint. " << endl;
  cout << "sizes are : " << iterations.size() << " " << actions.size() << " " << cutoffFreqs.size() << " " << nPoints.size();
  
  cout << " " << metrics.size() << endl;
  cout << "first elements are " << iterations.getFirst() << " ";
  cout << actions.getFirst() << " " << cutoffFreqs.getFirst() << " ";
  cout << nPoints.getFirst() << " " << metrics.getFirst() << " " << endl;
  */
  //cout << "action size : " << actions.size() << endl;
  // retrieve bounds
  juce::Rectangle<int> bounds = getLocalBounds();
  // lower part for monitoring
  juce::Rectangle<int> lowerHalf = bounds.removeFromBottom(bounds.getHeight() / 2);
  // remove a bit of margin
  int borderMargin = 35;
  lowerHalf = lowerHalf.reduced(borderMargin);
  
  int innerMargin = 35;
  
  // Divide lower half into 4 equal parts
  int w = (lowerHalf.getWidth()-innerMargin) / 2;
  int h = (lowerHalf.getHeight()-innerMargin) / 2;
  int x0 = lowerHalf.getX();
  int y0 = lowerHalf.getY();
  juce::Rectangle<int> r1(x0, y0, w, h);
  juce::Rectangle<int> r2(x0 + 1*w + innerMargin, y0, w, h);
  juce::Rectangle<int> r3(x0, y0 + 1*h + innerMargin, w, h);
  juce::Rectangle<int> r4(x0 + 1*w+innerMargin, y0 + 1*h + innerMargin, w, h);
  
  // draw action evolution in first recangle
  paintOneMonitoredQuantity(g, r3, "Action", actions);
  //paintOneMonitoredQuantity(g, r2, "Cutoff frequency", cutoffFreqs);
  //paintOneMonitoredQuantity(g, r4, "Convergence", convergence);
  paintOneMonitoredQuantity(g, r4, "H", absH, "log");
  //paintOneMonitoredQuantity(g, r3, "nPoints", nPoints);
  //paintOneMonitoredQuantity(g, r4, "Metric", metrics);
  
  //g.setColour(NORMAL_COLOR);
  //g.drawRect(r1);
  //g.drawRect(r2);
  //g.drawRect(r3);
  //g.drawRect(r4);
  
  
}



void NEPUI::resized()
{
    juce::Rectangle<int> r = getLocalBounds();
    editorUI->setBounds(r.reduced(10));
    vp.setBounds(r);
    repaint();
}


bool NEPUI::keyPressed(const KeyPress &e)
{
  if (e.getKeyCode() == KeyPress::spaceKey)
  {
    /*
    if (simul->isThreadRunning())
      simul->cancelTrigger->trigger();
    else
    {
      cout << "HERE ?" << endl;
      entityHistory.clear();
      entityColors.clear();
      simul->startTrigger->trigger();
    }
     */
  }

  return false;
}

void NEPUI::timerCallback()
{

}


void NEPUI::newMessage(const NEP::NEPEvent &ev)
{
  switch (ev.type)
  {
    case NEP::NEPEvent::WILL_START:
    {
      iterations.clear();
      actions.clear();
      cutoffFreqs.clear();
      nPoints.clear();
      metrics.clear();
      convergence.clear();
      absH.clear();
    }
    break;

    case NEP::NEPEvent::NEWSTEP:
    {
      iterations.add(ev.curStep);
      actions.add(ev.action);
      //cutoffFreqs.add(ev.cutofffreq);
      //nPoints.add( (double) ev.npoints);
      absH = ev.H;
      //metrics.add(ev.metric);
      //convergence.add(ev.convergenceFraction);
      repaint();
    }
    break;

    case NEP::NEPEvent::ERROR:
    {
      iterations.clear();
      actions.clear();
      cutoffFreqs.clear();
      nPoints.clear();
      metrics.clear();
      convergence.clear();
      absH.clear();
      repaint();
    }
    break;

  }
}


void NEPUI::newMessage(const ContainerAsyncEvent &e)
{
}


