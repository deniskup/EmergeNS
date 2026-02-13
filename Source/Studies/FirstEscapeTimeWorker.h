/*
  ==============================================================================

  FirstEscapeTime.h
  Created: Feb. 2026
  Author:  thkosc

  ==============================================================================
*/

#include "JuceHeader.h"
#include "Simulation/Simulation.h"
#include "Simulation/KineticLaw.h"


struct Snapshot
{
  ConcentrationGrid concgrid;
  float time;
  int run;
};

struct Escape
{
  float time;
  int startSteadyState;
  int escapeSteadyState;
};

class FirstEscapeTimeWorker : public juce::Thread
{
public:
    FirstEscapeTimeWorker(Simulation& sim)
        : juce::Thread("FirstEscapeTimeWorker"),
          simul(sim)
    {
      kinetics = new KineticLaw(false, 0.); // input parameters are for stochasticity
    }

    ~FirstEscapeTimeWorker() override
    {
        signalThreadShouldExit();
        workAvailable.signal();
        stopThread(2000);
    }
  
    void setConfig(map<String, String>);
  
    void reset();

    void submitSnapshot(const ConcentrationGrid& cg, float time, int run);
  
    void clearSnapshots(const int);
  
    //Array<float> escapeTimes;
    Array<Escape> escapes;
    OwnedArray<SimEntity> entities;
    OwnedArray<SimReaction> reactions;

private:
  
    void run() override; // the actual thread
  
    int identifyAttractionBasin(const Snapshot&);
  
    float distanceFromSteadyState(State sst);
  
    SimEntity * getSimEntityForID(const size_t idToFind);
  
    void writeResultsToFile();
  
    KineticLaw * kinetics;
    
    bool hasStoredEscapeTime = false;

    // === Synchronisation ===
    juce::WaitableEvent workAvailable;

    // === Données partagées (protégées) ===
    juce::CriticalSection dataLock;

    //ConcentrationGrid pendingGrid;
    //float pendingTime { 0.f };
    std::queue<Snapshot> pendingSnapshots;

    // === Références ===
    Simulation& simul;
  
    int patchid = 0; // hardcoded patch in which this study takes place.
    float precision = 1e-5; // precision up to which the steady state is determined
    float escapeTimePrecision = 10; // every 'exitTimePrecision', check where the system is
    int startSteadyState = 0;
    // In principle not designed to perform in heterogeneous space, it will complain about it otherwise
    float dt_study = 0.1; // time step used to identify in which attraction basin the system is
    bool debug = false; // if true, will request thread simulation to proceed to next run as soon as an escape is detected
    String network = "./network.ens";
    String outputfilename = "./output_escapeTimeStudy.csv";
    int superRun = 0;


  
    Array<int> runsTreated;

};

