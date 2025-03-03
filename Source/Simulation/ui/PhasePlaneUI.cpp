#include "PhasePlaneUI.h"


//RunUI::RunUI(Run* run) :
//    BaseItemUI(run)
//RunUI::RunUI(String &name) : ShapeShifterContentComponent(name)
                          //settings(Run::getInstance())
RunUI::RunUI() : ShapeShifterContentComponent("")
{
  editorUI.reset(new GenericControllableContainerEditor(run, true));
  addAndMakeVisible(editorUI.get());
    
}

RunUI::~RunUI()
{
}

void RunUI::resized()
{
  Rectangle<int> r = getLocalBounds();
  editorUI->setBounds(r.reduced(10));
}

/*
void RunUI::resizedInternalHeader(Rectangle<int> &r)
{
   
}
*/

/*
RunManagerUI::RunManagerUI() :
  BaseManagerShapeShifterUI(RunManager::getInstance()->niceName, RunManager::getInstance())
{
  addExistingItems();
}

RunManagerUI::~RunManagerUI()
{
}
*/


PhasePlaneUI::PhasePlaneUI() : ShapeShifterContentComponent(PhasePlane::getInstance()->niceName),
                               pp(PhasePlane::getInstance())
{

    pp->addPhasePlaneListener(this);

    editorUI.reset(new GenericControllableContainerEditor(pp, true));
    addAndMakeVisible(editorUI.get());

/*
    startUI.reset(pp->start->createButtonUI());
    drawUI.reset(pp->draw->createButtonUI());
    startDrawUI.reset(pp->startDraw->createButtonUI());
    nRunsUI.reset(pp->nRuns->createStepper());
  
    startUI->setSize(100, 20);
    drawUI->setSize(100, 20);
    startDrawUI->setSize(100, 20);
    nRunsUI->setSize(100, 20);
  
    addAndMakeVisible(startUI.get());
    addAndMakeVisible(drawUI.get());
    addAndMakeVisible(startDrawUI.get());
    addAndMakeVisible(nRunsUI.get());
*/
  
}

PhasePlaneUI::~PhasePlaneUI()
{
    pp->removePhasePlaneListener(this);
}

void PhasePlaneUI::resized()
{
  
    Rectangle<int> r = getLocalBounds();
    editorUI->setBounds(r.reduced(10));
/*
    r.removeFromTop(8);
    Rectangle<int> hr = r.removeFromTop(20);
   

  
    float buttonWidth = hr.getWidth() / 3.;
    startUI->setBounds(hr.removeFromLeft(buttonWidth));
    hr.removeFromLeft(20);
    drawUI->setBounds(hr.removeFromLeft(buttonWidth));
    hr.removeFromLeft(20);
    startDrawUI->setBounds(hr.removeFromLeft(buttonWidth));
    hr.removeFromLeft(20);
  
    r.removeFromTop(8);
    hr = r.removeFromTop(20);
    hr.reduce(nRunsUI->getWidth(), 0);
    nRunsUI->setBounds(hr);
*/
}

void PhasePlaneUI::updatePhasePlaneUI(PhasePlane *){
    //NLOG("GenerationUI","Repaint");
    //repaint();
    editorUI->resetAndBuild();
}
   
