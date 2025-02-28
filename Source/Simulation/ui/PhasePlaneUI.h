#pragma once

#include "../PhasePlane.h"

using namespace std;


class RunUI :
    public BaseItemUI<Run>
{
public:
    RunUI(Run* run);
    ~RunUI();

    void resizedInternalHeader(Rectangle<int> &r) override;
};


/*
class RunManagerUI :
    public BaseManagerShapeShifterUI<RunManager, Run, RunUI>
{
public:
    RunManagerUI();
    ~RunManagerUI();

    static RunManagerUI* create(const String& name) { return new RunManagerUI(); }

};
*/


class PhasePlaneUI : public ShapeShifterContentComponent,
            public PhasePlane::PhasePlaneListener
{
public:
    PhasePlaneUI();
    ~PhasePlaneUI();

    PhasePlane * pp;
    
    std::unique_ptr<GenericControllableContainerEditor> editorUI;
  
    unique_ptr<TriggerUI> startUI;
    unique_ptr<TriggerUI> drawUI;
    unique_ptr<TriggerUI> startDrawUI;
  
    unique_ptr<IntStepperUI> nRunsUI;



    // std::unique_ptr<IntStepperUI> numLevelsUI;
    // std::unique_ptr<IntStepperUI> entitiesPerLevelUI;
    // std::unique_ptr<IntStepperUI> maxReactionsPerEntityUI;
    // std::unique_ptr<IntStepperUI> avgNumShowUI;
    
    //local floatparameter
    //std::unique_ptr<FloatParameter> maxC;
    //std::unique_ptr<FloatParameterLabelUI> maxCUI;

    //void paint(juce::Graphics &) override;
    void resized() override;

    static PhasePlaneUI *create(const String &name) { return new PhasePlaneUI(); }

    void updatePhasePlaneUI(PhasePlane *) override;

};
