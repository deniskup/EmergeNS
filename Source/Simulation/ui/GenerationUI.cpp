
#include "GenerationUI.h"

GenerationUI::GenerationUI() : ShapeShifterContentComponent(Generation::getInstance()->niceName),
                               gener(Generation::getInstance())
{
    // maxStepsUI.reset(gener->maxSteps->createStepper());
    // dtUI.reset(gener->dt->createLabelParameter());
    // dtUI->setSuffix(" s");
    // totalTimeUI.reset(gener->totalTime->createLabelParameter());
    // totalTimeUI->setSuffix(" s");
    // // curStepUI.reset(gener->curStep->createSlider());
    // maxConcentUI.reset(gener->maxConcent->createLabelParameter());
    // startUI.reset(gener->startTrigger->createButtonUI());
    // cancelUI.reset(gener->cancelTrigger->createButtonUI());
    // realTimeUI.reset(gener->realTime->createToggle());

    // local parameter, won't be saved in the file.
    // maxC.reset(new FloatParameter("MaxC","descr",5.f,0));
    // maxCUI.reset(maxC->createLabelParameter())

    // addAndMakeVisible(dtUI.get());
    // addAndMakeVisible(totalTimeUI.get());
    // addAndMakeVisible(maxConcentUI.get());
    // addAndMakeVisible(startUI.get());
    // addAndMakeVisible(cancelUI.get());
    // addAndMakeVisible(realTimeUI.get());

    // curStepUI->customLabel = "Progress";

  
}

GenerationUI::~GenerationUI()
{

}



void GenerationUI::resized()
{
    // Rectangle<int> r = getLocalBounds();
    // Rectangle<int> hr = r.removeFromTop(27).reduced(2);
    // // maxStepsUI->setBounds(hr.removeFromLeft(200));
    // hr = hr.withSizeKeepingCentre(500, 25);
    // dtUI->setBounds(hr.removeFromLeft(100));
    // hr.removeFromLeft(20);
    // totalTimeUI->setBounds(hr.removeFromLeft(200));
    // realTimeUI->setBounds(hr.removeFromRight(100));
    // r.removeFromTop(10);
    // hr = r.removeFromTop(25);
    // hr = hr.withSizeKeepingCentre(420, 25);
    // startUI->setBounds(hr.removeFromLeft(100));
    // hr.removeFromLeft(30);
    // cancelUI->setBounds(hr.removeFromLeft(100));
    // hr.removeFromLeft(40);
    // maxConcentUI->setBounds(hr.removeFromLeft(150));
}


