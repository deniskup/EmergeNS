#pragma once

#include "../NEP.h"

using namespace std;



class NEPUI : public ShapeShifterContentComponent,
              public NEP::NEPListener
{
public:
    NEPUI();
    ~NEPUI();

    NEP * pp;
    
    std::unique_ptr<GenericControllableContainerEditor> editorUI;
  
    unique_ptr<TriggerUI> startUI;
    unique_ptr<TriggerUI> drawUI;
    unique_ptr<TriggerUI> startDrawUI;
  
    unique_ptr<IntStepperUI> nRunsUI;

    juce::Viewport vp;


    // std::unique_ptr<IntStepperUI> numLevelsUI;
    // std::unique_ptr<IntStepperUI> entitiesPerLevelUI;
    // std::unique_ptr<IntStepperUI> maxReactionsPerEntityUI;
    // std::unique_ptr<IntStepperUI> avgNumShowUI;
    
    //local floatparameter
    //std::unique_ptr<FloatParameter> maxC;
    //std::unique_ptr<FloatParameterLabelUI> maxCUI;

    //void paint(juce::Graphics &) override;
    void resized() override;

    static NEPUI *create(const String &name) { return new NEPUI(); }

    void updateNEPUI(NEP *) override;

};
