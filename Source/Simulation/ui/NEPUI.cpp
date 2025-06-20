#include "NEPUI.h"




NEPUI::NEPUI() : ShapeShifterContentComponent(NEP::getInstance()->niceName),
                               nep(NEP::getInstance())
{

    nep->addAsyncNEPListener(this);
    nep->addAsyncCoalescedNEPListener(this);
    //nep->addAsyncContainerListener(this);

    editorUI.reset(new GenericControllableContainerEditor(nep, true));
    addAndMakeVisible(editorUI.get());
  
    // set view component 
    addAndMakeVisible(vp);
    vp.setScrollBarsShown(true, true);
    vp.setScrollBarThickness(10);
    vp.setBounds(getLocalBounds());
    vp.setViewedComponent(editorUI.get(), false);
  

 
    // reset components
    startDescentUI.reset(nep->startDescent->createButtonUI());
    start_heteroclinic_studyUI.reset(nep->start_heteroclinic_study->createButtonUI());
    sst_stableUI.reset(nep->sst_stable->createUI());
    sst_saddleUI.reset(nep->sst_saddle->createUI());
    NiterationsUI.reset(nep->Niterations->createStepper());
    nPointsUI.reset(nep->nPoints->createStepper());
    cutoffFreqUI.reset(nep->cutoffFreq->createLabelParameter());
    action_thresholdUI.reset(nep->action_threshold->createLabelParameter());
    timescale_factorUI.reset(nep->timescale_factor->createLabelParameter());
  
    startDescentUI->setSize(150, 20);
    start_heteroclinic_studyUI->setSize(150, 20);
    sst_stableUI->setSize(150, 20);
    sst_saddleUI->setSize(150, 20);
    NiterationsUI->setSize(150, 20);
    nPointsUI->setSize(150, 20);
    cutoffFreqUI->setSize(150, 20);
    action_thresholdUI->setSize(150, 20);
    timescale_factorUI->setSize(150, 20);
  /*
    addAndMakeVisible(startDescentUI.get());
    addAndMakeVisible(start_heteroclinic_studyUI.get());
    addAndMakeVisible(sst_stableUI.get());
    addAndMakeVisible(sst_saddleUI.get());
    addAndMakeVisible(NiterationsUI.get());
    addAndMakeVisible(nPointsUI.get());
    addAndMakeVisible(cutoffFreqUI.get());
    addAndMakeVisible(action_thresholdUI.get());
    addAndMakeVisible(timescale_factorUI.get());
*/
  
}

NEPUI::~NEPUI()
{
  nep->removeAsyncNEPListener(this);
}


void NEPUI::paintOneMonitoredQuantity(juce::Graphics &g, Rectangle<int> r, String title, Array<double> data)
{
  if (data.size() == 0)
    return;
  jassert(data.size() == iterations.size());
  
  // retrieve max from array data
  float max = 0.;
  for (auto & v : data)
  {
    if (v>max)
      max = v;
  }
  jassert(max>0.);
  
  // draw rectagle around the box
  g.setColour(NORMAL_COLOR);
  g.drawRoundedRectangle(r.toFloat(), 4, 2.f);
  
  // find min and max of data
  float minX = *min_element(iterations.begin(), iterations.end());
  float maxX = *max_element(iterations.begin(), iterations.end());
  float minY = *min_element(data.begin(), data.end());
  float maxY = *max_element(data.begin(), data.end());
  
  float rangeX = maxX - minX;
  float rangeY = maxY - minY;
  if (rangeX<=0. || rangeY <= 0.)
    return;
  
  // convert data point into pixel coordinates
  auto toPixel = [&](double x, double y) -> Point<float>
  {
    float normX = (float)((x - minX) / rangeX);
    float normY = (float)((y - minY) / rangeY);
          
    float pixelX = r.getX() + normX * r.getWidth();
    float pixelY = r.getBottom() - normY * r.getHeight(); // Inversion Y

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
  }
  
  // draw the data
  g.setColour(juce::Colours::yellow);
  g.strokePath(*path, PathStrokeType(1.2));
  
  // draw axis
  g.setColour(NORMAL_COLOR);
  g.setFont(10.);
  int nticks = 4;
  int markwidth = 4;
  int markheight = 2;
  for (int i=0; i<=nticks; i++)
  {
    // Draw Y axis
    
    // x position of ticks = origin
    int x = r.getX();
    
    // y position of ticks
    float ii = i;
    float step = (float)r.getHeight() * ii / (float)nticks;
    int y = r.getY() + round(step);
    // draw the tick
    Rectangle<int> m1(x - markwidth / 2, y, markwidth, markheight);
    if (i != nticks & i != 0)
      g.drawRect(m1, markheight);

    // add corresponding concentration value

    // decide number of digits to print to labels
    int ndigits = 2;
    //int pow = round(log10(max)); //
    //if (pow<=2) ndigits = -pow + 2;

    // x position of ticks labels
    int xx = r.getX() - 40;
    Rectangle<int> tpos(xx, y, 50, 5);
    float conc = max * (1. - ii / nticks);
    stringstream ssconc;
    ssconc << fixed << setprecision(ndigits) << conc;
    string text = ssconc.str();
    g.drawText(text, tpos, Justification::centred, true);

    // draw X axis ticks and texts

    // y position of ticks = x axis
    y = r.getY() + r.getHeight();
    // x position of ticks
    step = (float)r.getWidth() * ii / (float)nticks;
    x = r.getX() + round(step);
    // draw the tick
    Rectangle<int> m2(x, y - markwidth / 2, markheight, markwidth);
    if (i != nticks & i != 0)
      g.drawRect(m2, markheight);

    // add corresponding time value
    // here decide the number of gigits to display
    //pow = round(log10(simul->totalTime->floatValue()));
    ndigits = 0;
    //if (pow<=2) ndigits = -pow + 2;

    //x -= 3 * pow;
    int boxwidth = 100;
    Rectangle<int> tpos2(x-boxwidth/2, y + 10, boxwidth, 5);
    float tot = iterations.getLast() * ii / nticks;
    stringstream sstime;
    sstime << fixed << setprecision(ndigits) << tot;
    text = sstime.str();
    if (i == 0)
      continue; // skip first tick
    else if (i > 0 && i <= nticks)
      g.drawText(text, tpos2, Justification::centred, true);
    
  } // end loop over ticks
  
  // add title
  g.setFont(15.);
  int titleX = r.getX() + r.getWidth()/2 - 50;
  int titleY = r.getY() - 20;
  Rectangle<int> titlepos(titleX, titleY, 100, 20);
  g.drawText(title, titlepos, Justification::centred, true);


  
}



void NEPUI::paint(juce::Graphics & g)
{
  //cout << "calling paint" << endl;
  //cout << "action size : " << actions.size() << endl;
  // retrieve bounds
  Rectangle<int> bounds = getLocalBounds();
  // lower part for monitoring
  Rectangle<int> lowerHalf = bounds.removeFromBottom(bounds.getHeight() / 2);
  // remove a bit of margin
  int borderMargin = 30;
  lowerHalf = lowerHalf.reduced(borderMargin);
  
  int innerMargin = 30;
  
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
  
  g.setColour(NORMAL_COLOR);
  
  //g.drawRect(r1);
  g.drawRect(r2);
  g.drawRect(r3);
  g.drawRect(r4);
  
  
}


/*


 // draw X and Y axis ticks with numerical labels
 int ncorr = nticks + 1;
 for (int i = 0; i <= ncorr; i++)
 {
   // draw Y axis ticks and text

   // x position of ticks = origin
   int x = simBounds.getX();
   // y position of ticks
   float ii = i;
   float step = (float)simBounds.getHeight() * ii / (float)ncorr;
   int y = simBounds.getY() + round(step);
   // draw the tick
   Rectangle<int> m1(x - markwidth / 2, y, markwidth, markheight);
   if (i != ncorr & i != 0)
     g.drawRect(m1, markheight);

   // add corresponding concentration value

   // decide number of digits to print to labels
   int ndigits = 0;
   int pow = round(log10(maxC)); //
   if (pow<=2) ndigits = -pow + 2;

   // x position of ticks labels
   int xx = simBounds.getX() - 50;
   Rectangle<int> tpos(xx, y, 50, 5);
   float conc = maxC * (1. - ii / ncorr);
   stringstream ssconc;
   ssconc << fixed << setprecision(ndigits) << conc;
   string text = ssconc.str();
   g.drawText(text, tpos, Justification::centred, true);

   // draw X axis ticks and texts

   // y position of ticks = x axis
   y = simBounds.getY() + simBounds.getHeight();
   // x position of ticks
   step = (float)simBounds.getWidth() * ii / (float)ncorr;
   x = simBounds.getX() + round(step);
   // draw the tick
   Rectangle<int> m2(x, y - markwidth / 2, markheight, markwidth);
   if (i != ncorr & i != 0)
     g.drawRect(m2, markheight);

   // add corresponding time value
   // here decide the number of gigits to display
   pow = round(log10(simul->totalTime->floatValue()));
   ndigits = 0;
   if (pow<=2) ndigits = -pow + 2;

   //x -= 3 * pow;
   int boxwidth = 100;
   Rectangle<int> tpos2(x-boxwidth/2, y + 10, boxwidth, 5);
   float time = simul->totalTime->floatValue() * ii / ncorr;
   stringstream sstime;
   sstime << fixed << setprecision(ndigits) << time;
   text = sstime.str();
   if (i == 0)
     continue; // skip first tick
   else if (i > 0 && i <= ncorr)
     g.drawText(text, tpos2, Justification::centred, true);
 } // end loop over ticks

 */


void NEPUI::resized()
{
    Rectangle<int> r = getLocalBounds();
    editorUI->setBounds(r.reduced(10));
    vp.setBounds(r);
  /*
    Rectangle<int> area = getLocalBounds().removeFromBottom(getHeight() / 2).reduced(20);

    juce::FlexBox fb;
    fb.flexDirection = juce::FlexBox::Direction::row;
    fb.justifyContent = juce::FlexBox::JustifyContent::spaceAround;
    fb.alignItems = juce::FlexBox::AlignItems::center;

     if (startDescentUI)
         fb.items.add(juce::FlexItem(*startDescentUI).withWidth(150).withHeight(20));

     fb.performLayout(area);
  */
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
  /*
  if (shouldRepaint)
  {
    repaint();
    shouldRepaint = false;
  }
  */
}

void NEPUI::newMessage(const NEP::NEPEvent &ev)
{
  switch (ev.type)
  {
    case NEP::NEPEvent::UPDATEPARAMS:
    {
    }
    case NEP::NEPEvent::WILL_START:
    {
      iterations.clear();
      actions.clear();
    }
    case NEP::NEPEvent::STARTED:
    {
    }
    case NEP::NEPEvent::NEWSTEP:
    {
      iterations.add(ev.curStep);
      actions.add(ev.action);
      repaint();
    }
    case NEP::NEPEvent::FINISHED:
    {
    }
  }
}


void NEPUI::newMessage(const ContainerAsyncEvent &e)
{

}


