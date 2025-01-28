
#include "SimulationUI.h"

SimulationUI::SimulationUI() : ShapeShifterContentComponent(Simulation::getInstance()->niceName),
							   simul(Simulation::getInstance())
//    saveSimBT("Save"),
//    loadSimBT("Load")
// uiStep(1)
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
	restartUI.reset(simul->restartTrigger->createButtonUI());
	cancelUI.reset(simul->cancelTrigger->createButtonUI());
	// autoLoadUI.reset(simul->loadToManualByDefault->createToggle());
	autoScaleUI.reset(simul->autoScale->createToggle());
	ignoreFreeEnergyUI.reset(simul->ignoreFreeEnergy->createToggle());
	ignoreBarriersUI.reset(simul->ignoreBarriers->createToggle());
	stochasticityUI.reset(simul->stochasticity->createToggle());
	detectEqUI.reset(simul->detectEquilibrium->createToggle());
	epsilonEqUI.reset(simul->epsilonEq->createLabelParameter());
	setCACUI.reset(simul->setCAC->createUI());
	setSteadyStateUI.reset(simul->setSteadyState->createUI());

	// local parameter, won't be saved in the file.
	// maxC.reset(new FloatParameter("MaxC","descr",5.f,0));
	// maxCUI.reset(maxC->createLabelParameter())

	dtUI->setSize(150, 20);
	totalTimeUI->setSize(200, 20);
	perCentUI->setSize(100, 20);
	maxConcentUI->setSize(150, 20);
	genUI->setSize(100, 20);
	startUI->setSize(100, 20);
	genstartUI->setSize(100, 20);
	restartUI->setSize(100, 20);
	cancelUI->setSize(100, 20);
	// autoLoadUI->setSize(130, 20);
	autoScaleUI->setSize(100, 20);
	pointsDrawnUI->setSize(150, 20);
	detectEqUI->setSize(120, 20);
	epsilonEqUI->setSize(100, 20);
	setCACUI->setSize(100, 20);
	setSteadyStateUI->setSize(100, 20);

	addAndMakeVisible(dtUI.get());
	addAndMakeVisible(totalTimeUI.get());
	addAndMakeVisible(maxConcentUI.get());
	addAndMakeVisible(genUI.get());
	addAndMakeVisible(startUI.get());
	addAndMakeVisible(genstartUI.get());
	addAndMakeVisible(restartUI.get());
	addAndMakeVisible(cancelUI.get());
	addAndMakeVisible(autoScaleUI.get());
	// addAndMakeVisible(autoLoadUI.get());
	addAndMakeVisible(perCentUI.get());
	addAndMakeVisible(pointsDrawnUI.get());
	addAndMakeVisible(ignoreFreeEnergyUI.get());
	addAndMakeVisible(ignoreBarriersUI.get());
	addAndMakeVisible(stochasticityUI.get());
	addAndMakeVisible(detectEqUI.get());
	addAndMakeVisible(epsilonEqUI.get());
	addAndMakeVisible(setCACUI.get());
	addAndMakeVisible(setSteadyStateUI.get());

	// saveSimBT.addListener(this);
	// addAndMakeVisible(&saveSimBT);

	// loadSimBT.addListener(this);
	// addAndMakeVisible(&loadSimBT);

	addAndMakeVisible(paramsLabel);
	paramsLabel.setJustificationType(Justification::centred);
	paramsLabel.setText("express mode", dontSendNotification);

	// maxConcentUI->setVisible(!simul->autoScale->boolValue());
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

	if (simul->shouldUpdate)
	{
		simul->updateParams();
		simul->shouldUpdate = false;
	}

	if (simul->autoScale->boolValue())
	{
		simul->maxConcent->setValue(simul->recordDrawn * 1.01);
	}
	float maxC = simul->maxConcent->floatValue();
	// (Our component is opaque, so we must completely fill the background with a solid colour)
	g.fillAll(BG_COLOR);

	// for alignment of simulation and RACs
	int leftMargin = 50;
	int rightMargin = 40;

	int extraMargin = leftMargin - rightMargin;
	simBounds = getLocalBounds().withTop(100).withTrimmedBottom(150).withLeft(extraMargin).reduced(rightMargin);
	simBounds.setWidth(simBounds.getWidth() - 20); // extra room on the right for bottom right tick

	// g.setFont(12);
	g.setColour(NORMAL_COLOR);
	g.drawRoundedRectangle(simBounds.toFloat(), 4, 3.f);
	// g.setColour(Colours::white.withAlpha(simul->isThreadRunning() ? .1f : .005f));
	// g.fillRoundedRectangle(simBounds.toFloat(), 4);

	g.setColour(Colours::white);
	g.setFont(14);
	Rectangle<int> botBounds = getLocalBounds().removeFromBottom(50);
	String paramsToDisplay;

	if (simul->entities.isEmpty())
		paramsToDisplay << "No simulation loaded";
	else
	{
		paramsToDisplay << simul->entities.size() << " entities (" << simul->primEnts.size() << " primary)        ";
		// paramsToDisplay << ((simul->numLevels == -1) ? "?" : String(simul->numLevels)) << " levels         ";
		paramsToDisplay << simul->reactions.size() << " reactions\n\n";
		// paramsToDisplay << simul->entitiesDrawn.size() << " drawn entities        ";
		paramsToDisplay << (simul->PACsGenerated ? String(simul->pacList->cycles.size()) : "?") << " PACs        ";
		int bCACs = simul->pacList->basicCACs.size();
		paramsToDisplay << (simul->PACsGenerated ? String(bCACs) : "?") << " CACs ";
		if (bCACs > 0 && simul->PACsGenerated)
			paramsToDisplay << " (" << String(simul->pacList->CACs.size() - bCACs) << " multiCACs)\n\n";
	}

	paramsLabel.setText(paramsToDisplay, dontSendNotification);

	if (simul->isThreadRunning() && !simul->realTime->boolValue()) // si pas option realTime
		return;
	if (entityHistory.isEmpty())
		return;
	if (simul->express)
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

	// draw axis
	int ncorr = nticks + 1;
	for (int i = 0; i <= ncorr; i++)
	{
		// draw Y axis

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
		int pow = 0;
		float div = 1.;
		while (maxC / div > 1)
		{
			pow++;
			div *= 10.;
		}
		int ndigits = 1;
		if (pow > 1)
			ndigits = 0;

		Rectangle<int> tpos(simBounds.getX() - 25, y, 50, 5);
		float conc = maxC * (1. - ii / ncorr);
		stringstream ssconc;
		ssconc << fixed << setprecision(ndigits) << conc;
		string text = ssconc.str();
		g.drawText(text, tpos, Justification::left, true);

		// draw X axis

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
		pow = 0;
		div = 1.;
		while (simul->totalTime->floatValue() / div > 1)
		{
			pow++;
			div *= 10.;
		}
		ndigits = 1;
		if (pow > 1)
			ndigits = 0;

		x -= 3 * pow;
		Rectangle<int> tpos2(x, y + 10, 100, 5);
		float time = simul->totalTime->floatValue() * ii / ncorr;
		stringstream sstime;
		sstime << fixed << setprecision(ndigits) << time;
		text = sstime.str();
		if (i == 0)
			continue; // skip first tick
		else if (i > 0 && i < ncorr)
			g.drawText(text, tpos2, Justification::left, true);
		else if (i == ncorr)
		{
			if (pow >= 4)
			{
				tpos2.setX(tpos2.getX() - 15);
			}
			g.drawText(text, tpos2, Justification::left, true);
		}

	} // end loop over ticks

} // end method paint

void SimulationUI::resized()
{
	Rectangle<int> r = getLocalBounds();
	Rectangle<int> hr = r.removeFromTop(firstLineHeight);

	int width1 = dtUI->getWidth() + 20 + detectEqUI->getWidth() + 15 + epsilonEqUI->getWidth() + 15 + totalTimeUI->getWidth() + 20 + pointsDrawnUI->getWidth();

	hr.reduce((hr.getWidth() - width1) / 2, 0);

	dtUI->setBounds(hr.removeFromLeft(dtUI->getWidth()));
	hr.removeFromLeft(20);
	detectEqUI->setBounds(hr.removeFromLeft(detectEqUI->getWidth()));
	hr.removeFromLeft(15);
	epsilonEqUI->setBounds(hr.removeFromLeft(epsilonEqUI->getWidth()));
	hr.removeFromLeft(15);
	totalTimeUI->setBounds(hr.removeFromLeft(totalTimeUI->getWidth()));
	hr.removeFromLeft(20);
	pointsDrawnUI->setBounds(hr.removeFromLeft(pointsDrawnUI->getWidth()));
	// hr.removeFromLeft(40);
	// autoLoadUI->setBounds(hr.removeFromRight(autoLoadUI->getWidth()));

	r.removeFromTop(8);
	hr = r.removeFromTop(secondLineHeight);

	// compute button width
	const float nButtons = 5;
	float buttonWidth = (hr.getWidth() - 20 * (nButtons) - (50 + autoScaleUI->getWidth() + 10 + maxConcentUI->getWidth())) / nButtons;
	// int width2 = genUI->getWidth() + 20 + startUI->getWidth() + 20 + restartUI->getWidth() + 20 + genstartUI->getWidth() + 20 + cancelUI->getWidth() + 50 + autoScaleUI->getWidth() + 10 + maxConcentUI->getWidth();
	hr.reduce(10, 0);

	// buttons
	genstartUI->setBounds(hr.removeFromLeft(buttonWidth));
	hr.removeFromLeft(20);

	genUI->setBounds(hr.removeFromLeft(buttonWidth));
	hr.removeFromLeft(20);

	restartUI->setBounds(hr.removeFromLeft(buttonWidth));
	hr.removeFromLeft(20);

	startUI->setBounds(hr.removeFromLeft(buttonWidth));
	hr.removeFromLeft(20);

	cancelUI->setBounds(hr.removeFromLeft(buttonWidth));
	hr.removeFromLeft(50);
	autoScaleUI->setBounds(hr.removeFromLeft(autoScaleUI->getWidth()));
	hr.removeFromLeft(10);
	maxConcentUI->setBounds(hr.removeFromLeft(maxConcentUI->getWidth()));

	r.removeFromTop(8);
	perCentUI->setBounds(r.removeFromTop(25).reduced(4));

	Rectangle<int> br = r.removeFromBottom(150);
	// Rectangle<int> butr = br.removeFromRight(100);
	// saveSimBT.setBounds(butr.removeFromTop(50).reduced(10));
	// loadSimBT.setBounds(butr.removeFromBottom(50).reduced(10));

	Rectangle<int> explore = br.removeFromBottom(40).reduced(5);

	ignoreFreeEnergyUI->setBounds(explore.removeFromLeft(145));
	explore.removeFromLeft(20);
	ignoreBarriersUI->setBounds(explore.removeFromLeft(120));
	explore.removeFromLeft(20);
	stochasticityUI->setBounds(explore.removeFromLeft(110));

	setCACUI->setBounds(explore.removeFromRight(setCACUI->getWidth()));
	explore.removeFromRight(10);
	setSteadyStateUI->setBounds(explore.removeFromRight(setSteadyStateUI->getWidth()));

	paramsLabel.setBounds(br.reduced(10));
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

// void SimulationUI::buttonClicked(Button *b)
// {
// if (b == &saveSimBT)
// {

//     FileChooser *chooser(new FileChooser("Select a file", File(), "*.sim"));

//     int openFlags = FileBrowserComponent::saveMode;
//     openFlags = openFlags | FileBrowserComponent::FileChooserFlags::canSelectFiles;

//     chooser->launchAsync(openFlags, [this](const FileChooser &fc)
//                          {
//                              File f = fc.getResult();
//                              delete &fc;

//                              // save the sim here
//                              var data = simul->toJSONData();
//                              f.deleteFile();
//                              FileOutputStream output(f);
//                              JSON::writeToStream(output, data);
//                              LOG("Saved to " << f.getFullPathName()); });
// }

// if (b == &loadSimBT)
// {

//     FileChooser *chooser(new FileChooser("Select a file", File(), "*.sim"));

//     int openFlags = FileBrowserComponent::openMode;
//     openFlags = openFlags | FileBrowserComponent::FileChooserFlags::canSelectFiles;

//     chooser->launchAsync(openFlags, [this](const FileChooser &fc)
//                          {
//         File f = fc.getResult();
//         delete &fc;

//         // load the sim here
//         var data = JSON::parse(f);
//         simul->importJSONData(data);
//         LOG("Loaded from " << f.getFullPathName()); });

// }
//}

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
		// print for debug
		//   NLOG("Value", ev.entityValues[0]);

		if (simul->realTime->boolValue())
			shouldRepaint = true;
	}
	break;

	case Simulation::SimulationEvent::FINISHED:
	{
		shouldRepaint = true;
		// resized();
		// repaint();
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
			//	maxConcentUI->setVisible(!simul->autoScale->boolValue());
			shouldRepaint = true;
		}
		else if (e.targetControllable == simul->maxConcent)
		{
			shouldRepaint = true;
		}
		else if (e.targetControllable == simul->detectEquilibrium)
		{
			epsilonEqUI->setVisible(simul->detectEquilibrium->boolValue());
			shouldRepaint = true;
		}
	}
}
