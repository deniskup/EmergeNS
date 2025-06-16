#include "NEPUI.h"




NEPUI::NEPUI() : ShapeShifterContentComponent(NEP::getInstance()->niceName),
                               pp(NEP::getInstance())
{

    pp->addNEPListener(this);

    editorUI.reset(new GenericControllableContainerEditor(pp, true));
    addAndMakeVisible(editorUI.get());
  
    // set view component 
    addAndMakeVisible(vp);
    vp.setScrollBarsShown(true, true);
    vp.setScrollBarThickness(10);
    vp.setBounds(getLocalBounds());
    vp.setViewedComponent(editorUI.get(), false);



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

NEPUI::~NEPUI()
{
    pp->removeNEPListener(this);
}

void NEPUI::resized()
{
  
    Rectangle<int> r = getLocalBounds();
    editorUI->setBounds(r.reduced(10));
    vp.setBounds(r);
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

void NEPUI::updateNEPUI(NEP *){
    //NLOG("GenerationUI","Repaint");
    //repaint();
    editorUI->resetAndBuild();
}
   
