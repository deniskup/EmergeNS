#include "PhasePlaneUI.h"

PhasePlaneUI::PhasePlaneUI() : ShapeShifterContentComponent(PhasePlane::getInstance()->niceName),
                               pp(PhasePlane::getInstance())
{
    //option: boucle sur les controllables avec createDefaultUI();

    // numLevelsUI.reset(gener->numLevels->createStepper());
    // entitiesPerLevelUI.reset(gener->entitiesPerLevel->createStepper());
    // maxReactionsPerEntityUI.reset(gener->maxReactionsPerEntity->createStepper());
    // avgNumShowUI.reset(gener->avgNumShow->createStepper());

    // addAndMakeVisible(numLevelsUI.get());
    // addAndMakeVisible(entitiesPerLevelUI.get());
    // addAndMakeVisible(maxReactionsPerEntityUI.get());
    // addAndMakeVisible(avgNumShowUI.get());

    pp->addPhasePlaneListener(this);

    editorUI.reset(new GenericControllableContainerEditor(pp, true));
    addAndMakeVisible(editorUI.get());

}

PhasePlaneUI::~PhasePlaneUI()
{
    pp->removePhasePlaneListener(this);
}

void PhasePlaneUI::resized()
{
    Rectangle<int> r = getLocalBounds();
    editorUI->setBounds(r.reduced(10));
    // r.removeFromTop(10);
    // Rectangle<int> hr = r.removeFromTop(27).reduced(2);
    // // maxStepsUI->setBounds(hr.removeFromLeft(200));
    // numLevelsUI->setBounds(hr);
    // r.removeFromTop(10);
    // entitiesPerLevelUI->setBounds(r.removeFromTop(25));
    // r.removeFromTop(10);
    // maxReactionsPerEntityUI->setBounds(r.removeFromTop(25));
    // r.removeFromTop(10);
    // avgNumShowUI->setBounds(r.removeFromTop(25));
}

void PhasePlaneUI::updatePhasePlaneUI(PhasePlane *){
    //NLOG("GenerationUI","Repaint");
    //repaint();
    editorUI->resetAndBuild();
}
   
