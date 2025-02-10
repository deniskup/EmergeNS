
#pragma once

#include "../Generation.h"

class GenerationUI : public ShapeShifterContentComponent,
            public Generation::GenerationListener
{
public:
    GenerationUI();
    ~GenerationUI();

    Generation *gener;
    
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

    static GenerationUI *create(const String &name) { return new GenerationUI(); }

    void updateGenUI(Generation *) override;

};