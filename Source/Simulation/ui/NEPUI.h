#pragma once

#include "../NEP.h"

using namespace std;

//class SpaceUI : public ShapeShifterContentComponent,
//                public Simulation::AsyncSimListener,
//                public Space::AsyncSpaceListener,
//                public Timer,
//                public ContainerAsyncListener


class NEPUI : public ShapeShifterContentComponent,
              public NEP::AsyncNEPListener,
              public ContainerAsyncListener,
              public juce::Timer
{
public:
    NEPUI();
    ~NEPUI();

    NEP * nep;
    
    std::unique_ptr<GenericControllableContainerEditor> editorUI;
  
    juce::Viewport vp; // scrollable window

    // Action juce::array
    juce::Array<int> iterations;
    juce::Array<double> actions;
    juce::Array<double> cutoffFreqs;
    juce::Array<double> nPoints;
    juce::Array<double> metrics;
  
    void paintAxis(juce::Graphics &g, juce::Rectangle<int> bounds, juce::String type, int nticks, float max, int ndigits);
  
    void paintOneMonitoredQuantity(juce::Graphics &, juce::Rectangle<int>, juce::String, juce::Array<double>);

    void paint(juce::Graphics &) override;
  
    void resized() override;
  
    void timerCallback() override;
  
    bool keyPressed(const juce::KeyPress &e) override;

    void newMessage(const NEP::NEPEvent &e) override;

    void newMessage(const ContainerAsyncEvent &e) override;

    static NEPUI *create(const juce::String &name) { return new NEPUI(); }

    //void updateNEPUI(NEP *);

};
