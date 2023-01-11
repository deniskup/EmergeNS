
#pragma once

#include "../Generation.h"

class GenerationUI : public ShapeShifterContentComponent
{
public:
    GenerationUI();
    ~GenerationUI();

    Generation *gener;

    //std::unique_ptr<IntStepperUI> maxStepsUI;
    // std::unique_ptr<FloatParameterLabelUI> dtUI;
    // std::unique_ptr<FloatParameterLabelUI> totalTimeUI;
    // std::unique_ptr<IntSliderUI> curStepUI;
    // std::unique_ptr<FloatParameterLabelUI> maxConcentUI;
    // std::unique_ptr<TriggerUI> startUI;
    // std::unique_ptr<TriggerUI> cancelUI;
    // std::unique_ptr<BoolToggleUI> realTimeUI;

    
    //local floatparameter
    //std::unique_ptr<FloatParameter> maxC;
    //std::unique_ptr<FloatParameterLabelUI> maxCUI;

    //void paint(juce::Graphics &) override;
    void resized() override;

    static GenerationUI *create(const String &name) { return new GenerationUI(); }
};