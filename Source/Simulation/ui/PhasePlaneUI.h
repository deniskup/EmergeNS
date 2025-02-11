#pragma once

#include "../PhasePlane.h"

class PhasePlaneUI : public ShapeShifterContentComponent,
            public PhasePlane::PhasePlaneListener
{
public:
    PhasePlaneUI();
    ~PhasePlaneUI();

    PhasePlane * pp;
    
    std::unique_ptr<GenericControllableContainerEditor> editorUI;

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
