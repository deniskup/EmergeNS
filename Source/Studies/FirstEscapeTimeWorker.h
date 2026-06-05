/*
  ==============================================================================

  FirstEscapeTime.h
  Created: Feb. 2026
  Author:  thkosc

  ==============================================================================
*/

#pragma once

#include "JuceHeader.h"
#include "Simulation/Simulation.h"
#include "Simulation/KineticLaw.h"


class EscapeListener;

struct Snapshot
{
  ConcentrationGrid concgrid;
  float time;
  int run;
};

struct Escape
{
  int run;
  float time;
  int startSteadyState;
  int escapeSteadyState;
};

struct StudyParameters
{
  float precision;
  float escapeTimePrecision;
  float dt_study;
  int startSteadyState;
};

struct CRNSimulation
{
  // juce::Array<Patch>
  juce::OwnedArray<SimEntity> entities;
  juce::OwnedArray<SimReaction> reactions;
  juce::Array<SteadyState> arraySteadyStates; 
};

//class FirstEscapeTimeWorker : public juce::Thread
class FirstEscapeTimeJob : public juce::ThreadPoolJob
{
public:
    /*FirstEscapeTimeWorker(Simulation& sim)
        : juce::Thread("FirstEscapeTimeWorker"),
          simul(sim)
    {
      kinetics = new KineticLaw(false, 0.); // input parameters are for stochasticity
    }*/

      FirstEscapeTimeJob(EscapeListener& _listener, CRNSimulation& _crn, ConcentrationGrid cg,
      int _run, float _time, StudyParameters _studyParams)
       : 
      juce::ThreadPoolJob("FirstEscapeTimeJob"), listener(_listener), crn(_crn), snapConc(cg), 
      run(_run), time(_time), escapeTimePrecision(_studyParams.escapeTimePrecision), startSteadyState(_studyParams.startSteadyState),
      precision(_studyParams.precision), dt(_studyParams.dt_study)
      {
        kinetics = new KineticLaw(false, 0.); // input parameters are for stochasticity
        //entities = crn.entities;
        //reactions = crn.reactions;
        //snapConc = cg;
        //escapes = _escapes;
      }


    ~FirstEscapeTimeJob() override
    {
        signalJobShouldExit();
        //workAvailable.signal();
        //stopThread(2000);
    }

    JobStatus runJob() override;
  
    //void setConfig(map<juce::String, juce::String>);
  

    void submitSnapshot(const ConcentrationGrid& cg, float time, int run);
  
    void clearSnapshots(const int);


private:
  
    //void run() override; // the actual thread
  
    int identifyAttractionBasin();
  
    float distanceFromSteadyState(State sst);
  
    SimEntity * getSimEntityForID(const size_t idToFind);
  
    //void writeResultsToFile();
  
    KineticLaw * kinetics;
    
    bool hasStoredEscapeTime = false;

    // === Synchronisation ===
    //juce::WaitableEvent workAvailable;

    // === Données partagées (protégées) ===
    //juce::CriticalSection dataLock;

    //ConcentrationGrid pendingGrid;
    //float pendingTime { 0.f };
    //std::queue<Snapshot> pendingSnapshots;

    // === Références ===
    //Simulation& simul;

    CRNSimulation& crn;

    ConcentrationGrid snapConc;

    EscapeListener& listener;
  
    int patchid = 0; // hardcoded patch in which this study takes place.
    //float precision = 1e-5; // precision up to which the steady state is determined
    //float escapeTimePrecision = 10; // every 'exitTimePrecision', check where the system is
    //int startSteadyState = 0;
    // In principle not designed to perform in heterogeneous space, it will complain about it otherwise
    //float dt_study = 0.1; // time step used to identify in which attraction basin the system is
    //bool debug = false; // if true, will request thread simulation to proceed to next run as soon as an escape is detected
    //juce::String network = "./network.ens";
    //juce::String outputfilename = "./output_escapeTimeStudy.csv";
    //int superRun = 0;

    int run;
    float escapeTimePrecision;
    float time;
    int startSteadyState;
    float precision;
    float dt;
  

};

