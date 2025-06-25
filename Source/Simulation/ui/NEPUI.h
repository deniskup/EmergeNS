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
              public Timer
{
public:
    NEPUI();
    ~NEPUI();

    NEP * nep;
    
    std::unique_ptr<GenericControllableContainerEditor> editorUI;
  
    juce::Viewport vp; // scrollable window

    // Action array
    Array<int> iterations;
    Array<double> actions;
    Array<double> cutoffFreqs;
    Array<double> nPoints;
    Array<double> metrics;
  
    void paintAxis(juce::Graphics &g, Rectangle<int> bounds, String type, int nticks, float max, int ndigits);
  
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
