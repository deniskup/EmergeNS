#include "NEPUI.h"




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
void NEPUI::paintAxis(juce::Graphics &g, Rectangle<int> r, String type, int nticks, float max, int ndigits)
{
  g.setColour(NORMAL_COLOR);
  g.setFont(10.);
  
  int markwidth = 4;
  int markheight = 2;
  int textboxwidth = 25;
  int textboxheight = 5;
  int shiftXaxisLabels = 10;
  int shiftYaxisLabels = 25;

//  cout << "bounds : " << r.getX() << " " << r.getY() << " " << r.getWidth() << " " << r.getHeight() << endl;
//  cout << "type = " << type << ". ndigits = " << ndigits << endl;
  
  for (int i=0; i<=nticks; i++)
  //for (int i=0; i<=0; i++)
  {
    // Draw the tick marks
    int markX, markY;
    if (i>0 && i<nticks)
    {
      if (type == "X")
      {
        markX = r.getX() + round((float)r.getWidth() * (float) i / (float)nticks);
        markY = r.getY() + r.getHeight();
        //cout << "tick #" << i << ". xpos : " << markX << ". ypos : " << markY << endl;
        Rectangle<int> m(markX, markY - markwidth / 2, markheight, markwidth);
        g.drawRect(m, markheight);
      }
      else
      {
        markX = r.getX();
        markY = r.getY() + round((float)r.getHeight() * (float) i / (float)nticks);
        Rectangle<int> m(markX - markwidth / 2, markY, markwidth, markheight);
        g.drawRect(m, markheight);
      }
    }
    
  
    // ticks labels
    if (type == "X")
    {
      String label = "";
      if (i==0)
        label = String(iterations.getFirst());;
      if (i==nticks)
        label = String(iterations.getLast());
      int labelX = r.getX() + round((float)r.getWidth() * (float) i / (float)nticks) - textboxwidth/2;
      int labelY = r.getY() + r.getHeight() + shiftXaxisLabels;
      Rectangle<int> labelpos(labelX, labelY, textboxwidth, textboxheight);
      if (i==0 || i==nticks) // only display first and last values for x axis
        g.drawText(label, labelpos, Justification::centred, true);
    }
    else
    {
      // x position of ticks labels
      int labelX = r.getX() - shiftYaxisLabels;
      int labelY = r.getY() + round( (float) r.getHeight() * (1. - (float) i / (float) nticks) );
      Rectangle<int> labelpos(labelX, labelY, textboxwidth, textboxheight);
      //float val = max * (1. - (float) i / (float) nticks);
      float val = max * ( (float) i / (float) nticks);
      stringstream ssval;
      ssval << fixed << setprecision(ndigits) << val;
      string label = ssval.str();
      g.drawText(label, labelpos, Justification::centred, true);
    }
  } // end loop over ticks
  
  
}


void NEPUI::paintOneMonitoredQuantity(juce::Graphics &g, Rectangle<int> r, String title, Array<double> data)
{
  if (data.size() == 0)
    return;
  jassert(data.size() == iterations.size());
  //cout << "data type : " << title << ". size = " << data.size() << " vs Niter = " << iterations.size() << endl;
  
  //cout << "data " << title << " : ";
  //for (auto & el : data)
  //  cout << el << " ";
  //cout << endl;
  
  
  // retrieve max from array data
  /*auto max_it = max_element(data.begin(), data.end());
  float max = (max_it != data.end() ? *max_it : 1.0);
  cout << "title : " << title << ". max = " << max << endl;
  jassert(max>0.);
  */
  // draw rectagle around the box
  g.setColour(NORMAL_COLOR);
  g.drawRoundedRectangle(r.toFloat(), 4, 2.f);
  
  // find min and max of data
  double minX = *min_element(iterations.begin(), iterations.end());
  double maxX = *max_element(iterations.begin(), iterations.end());
  double minY = *min_element(data.begin(), data.end());
  double maxY = *max_element(data.begin(), data.end());
  double rangeX = maxX - minX;
  double rangeY = maxY - minY;
  
  if (rangeX == 0.)
  {
    rangeX = abs(maxX);
    minX = std::min(0., minX);
    maxX = std::max(0., maxX);
  }
  if (rangeY == 0.)
  {
    rangeY = abs(maxY);
    minY = std::min(0., minY);
    maxY = std::max(0., maxY);
  }
  
  /*
  if (title == "Action")
  {
    maxY += 1.1*rangeY;
    minY -= 1.1*rangeY;
  }
  else
  {
    minY = 0.;
    maxY *= 1.1; // little more room for esthetics
  }
   */
  
  // make little more room for plots
  maxY += 0.05*rangeY;
  if (title == "Action")
    minY -= 0.05*rangeY;
  rangeY = maxY - minY;
  //rangeY = maxY
    
  if (rangeX<0. || rangeY<0.)
    return;
  
  // convert data point into pixel coordinates
  auto toPixel = [&](double x, double y) -> Point<float>
  {
    float normX = (float)((x - minX) / rangeX);
    float normY = (float)((y - minY) / rangeY);
          
    float pixelX = r.getX() + normX * r.getWidth();
    float pixelY = r.getBottom() - normY * r.getHeight(); // Inversion Y
    //float pixelY = r.getY() - normY * r.getHeight(); // Inversion Y

    Point<float> pixPoint = {pixelX, pixelY};
    
    return pixPoint;
  };
  
  // start a path and init to first value
  Path * path = new Path();
  path->startNewSubPath(toPixel(iterations.getUnchecked(0), data.getUnchecked(0)));
  
  // add all points
  for (int k=1; k<data.size(); k++)
  {
    path->lineTo(toPixel(iterations.getUnchecked(k), data.getUnchecked(k)));
    if (title=="Action")
    {
      //cout << "rangeY : " << rangeY << endl;
      //cout << "action array = " << endl;
      //for (auto & el : data)
      //  cout << el << " ";
      //cout << endl;
      //cout << "rectangle coords : " << endl;
      //cout << r.getX() << " " << r.getRight() << " " << r.getBottom() << " " << r.getY() << endl;
      //auto pixPoint = toPixel(iterations.getUnchecked(k), data.getUnchecked(k));
      //cout << "adding point " << pixPoint.x << " " << pixPoint.y << endl;
    }
  }
  
  // draw the data
  juce::Colour col = juce::Colours::purple;
  if (title == "Action")
    col = juce::Colours::yellow;
  else if (title == "Cutoff frequency")
    col = juce::Colours::pink;
  else if (title == "nPoints")
    col = juce::Colours::powderblue;
  else if (title == "Metric")
    col = juce::Colours::orangered;
  g.setColour(col);
  g.strokePath(*path, PathStrokeType(1.2));
  
  // draw axis
  int nticksX = 4;
  int nticksY = 4;
  int ndigitsX = 0;
  int ndigitsY = 2;
  if (title == "nPoints")
    ndigitsY = 0;
  
  paintAxis(g, r, "X", nticksX, iterations.getLast(), ndigitsX);
  paintAxis(g, r, "Y", nticksY, maxY, ndigitsY);
  
  // add plot title
  g.setFont(15.);
  int titleboxwidth = 150;
  int titleX = r.getX() + r.getWidth()/2 - titleboxwidth/2;
  int titleY = r.getY() - 20;
  Rectangle<int> titlepos(titleX, titleY, titleboxwidth, 20);
  g.drawText(title, titlepos, Justification::centred, true);


  
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
  Rectangle<int> bounds = getLocalBounds();
  // lower part for monitoring
  Rectangle<int> lowerHalf = bounds.removeFromBottom(bounds.getHeight() / 2);
  // remove a bit of margin
  int borderMargin = 35;
  lowerHalf = lowerHalf.reduced(borderMargin);
  
  int innerMargin = 35;
  
  // Divide lower half into 4 equal parts
  int w = (lowerHalf.getWidth()-innerMargin) / 2;
  int h = (lowerHalf.getHeight()-innerMargin) / 2;
  int x0 = lowerHalf.getX();
  int y0 = lowerHalf.getY();
  Rectangle<int> r1(x0, y0, w, h);
  Rectangle<int> r2(x0 + 1*w + innerMargin, y0, w, h);
  Rectangle<int> r3(x0, y0 + 1*h + innerMargin, w, h);
  Rectangle<int> r4(x0 + 1*w+innerMargin, y0 + 1*h + innerMargin, w, h);
  
  // draw action evolution in first recangle
  paintOneMonitoredQuantity(g, r1, "Action", actions);
  paintOneMonitoredQuantity(g, r2, "Cutoff frequency", cutoffFreqs);
  paintOneMonitoredQuantity(g, r3, "nPoints", nPoints);
  paintOneMonitoredQuantity(g, r4, "Metric", metrics);
  
  //g.setColour(NORMAL_COLOR);
  //g.drawRect(r1);
  //g.drawRect(r2);
  //g.drawRect(r3);
  //g.drawRect(r4);
  
  
}



void NEPUI::resized()
{
    Rectangle<int> r = getLocalBounds();
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
    }
    break;

    case NEP::NEPEvent::NEWSTEP:
    {
      iterations.add(ev.curStep);
      actions.add(ev.action);
      cutoffFreqs.add(ev.cutofffreq);
      nPoints.add( (double) ev.npoints);
      metrics.add(ev.metric);
      repaint();
    }
    break;

  }
}


void NEPUI::newMessage(const ContainerAsyncEvent &e)
{
}


