#pragma once

#include "../NEP.h"

using namespace std;



class NEPUI : public ShapeShifterContentComponent,
              public NEP::AsyncNEPListener,
              public ContainerAsyncListener,
              public Timer
{
public:
    NEPUI();
    ~NEPUI();

    NEP * nep;
    
    std::unique_ptr<GenericControllableContainerEditor> editorUI;
  
  
    unique_ptr<TriggerUI> startDescentUI;
    unique_ptr<TriggerUI> start_heteroclinic_studyUI;
    unique_ptr<EnumParameterUI> sst_stableUI;
    unique_ptr<EnumParameterUI> sst_saddleUI;
    unique_ptr<IntStepperUI> NiterationsUI;
    unique_ptr<IntStepperUI> nPointsUI;
    unique_ptr<FloatParameterLabelUI> cutoffFreqUI;
    unique_ptr<FloatParameterLabelUI> action_thresholdUI;
    unique_ptr<FloatParameterLabelUI> timescale_factorUI;

  
    juce::Viewport vp; // scrollable window

    // Action array
    Array<int> iterations;
    Array<double> actions;
  
    void paintOneMonitoredQuantity(juce::Graphics &, Rectangle<int>, String, Array<double>);

    void paint(juce::Graphics &) override;
  
    void resized() override;
  
    void timerCallback() override;
  
    bool keyPressed(const KeyPress &e) override;

    void newMessage(const NEP::NEPEvent &e) override;

    void newMessage(const ContainerAsyncEvent &e) override;

    static NEPUI *create(const String &name) { return new NEPUI(); }

    //void updateNEPUI(NEP *);

};
