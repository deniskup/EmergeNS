#include "JuceHeader.h"
#include "Simulation/Simulation.h"
#include "Simulation/KineticLaw.h"

class FirstExitTimeWorker : public juce::Thread
{
public:
    FirstExitTimeWorker(Simulation& sim)
        : juce::Thread("FirstExitTimeWorker"),
          simulation(sim)
    {}

    ~FirstExitTimeWorker() override
    {
        signalThreadShouldExit();
        workAvailable.signal();
        stopThread(2000);
    }

    // Appelée depuis FirstExitTime (message thread)
    void submitSnapshot(const ConcentrationGrid& grid, float time);

private:
    void run() override;

    // === Synchronisation ===
    juce::WaitableEvent workAvailable;

    // === Données partagées (protégées) ===
    juce::CriticalSection dataLock;
    bool hasPendingWork { false };

    ConcentrationGrid pendingGrid;
    float pendingTime { 0.f };

    // === Références ===
    Simulation& simulation;
};
