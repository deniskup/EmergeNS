
#include "SettingsUI.h"

SettingsUI::SettingsUI() : ShapeShifterContentComponent(Settings::getInstance()->niceName),
                           settings(Settings::getInstance())
{
    // option: boucle sur les controllables avec createDefaultUI();
    editorUI.reset(new GenericControllableContainerEditor(settings, true));
    addAndMakeVisible(editorUI.get());
}

SettingsUI::~SettingsUI()
{
    // settings->removeSettingsListener(this);
}

void SettingsUI::resized()
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

// void SettingsUI::updateSettingsUI(Settings *){
// NLOG("SettingsUI","Repaint");
// repaint();
//  editorUI->resetAndBuild();
//}
