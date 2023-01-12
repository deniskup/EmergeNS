
#include "GenerationUI.h"

GenerationUI::GenerationUI() : ShapeShifterContentComponent(Generation::getInstance()->niceName),
                               gener(Generation::getInstance())
{
    numLevelsUI.reset(gener->numLevels->createStepper());
    entitiesPerLevelUI.reset(gener->entitiesPerLevel->createStepper());
    maxReactionsPerEntityUI.reset(gener->maxReactionsPerEntity->createStepper());
    avgNumShowUI.reset(gener->avgNumShow->createStepper());
    // TODO: add default UI like for BaseITems

    addAndMakeVisible(numLevelsUI.get());
    addAndMakeVisible(entitiesPerLevelUI.get());
    addAndMakeVisible(maxReactionsPerEntityUI.get());
    addAndMakeVisible(avgNumShowUI.get());
}

GenerationUI::~GenerationUI()
{
}

void GenerationUI::resized()
{
    Rectangle<int> r = getLocalBounds();
    r.removeFromTop(10);
    Rectangle<int> hr = r.removeFromTop(27).reduced(2);
    // maxStepsUI->setBounds(hr.removeFromLeft(200));
    numLevelsUI->setBounds(hr);
    r.removeFromTop(10);
    entitiesPerLevelUI->setBounds(r.removeFromTop(25));
    r.removeFromTop(10);
    maxReactionsPerEntityUI->setBounds(r.removeFromTop(25));
    r.removeFromTop(10);
    avgNumShowUI->setBounds(r.removeFromTop(25));
}
