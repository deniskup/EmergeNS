/*
  ==============================================================================

  FirstEscapeTime.h
  Created: Feb. 2026
  Author:  thkosc

  ==============================================================================
*/
#pragma once

#include "JuceHeader.h"
//#include "Simulation/Simulation.h"
//#include "Simulation/KineticLaw.h"
#include "FirstEscapeTimeWorker.h"


class EscapeListener
{
public:
    EscapeListener(){};
    virtual ~EscapeListener(){};

    virtual void signalEscapeDetected(const Escape&) = 0;

    virtual void signalJobFinished(int, int) = 0;
};



class FirstEscapeTime : public Simulation::AsyncSimListener,
                        public EscapeListener 
{
public:
  juce_DeclareSingleton(FirstEscapeTime, true);
  FirstEscapeTime();
  ~FirstEscapeTime();
    
  void setSimulationConfig(std::map<juce::String, juce::String>);
  
  void startStudy();
    
private:

  void copyReactionNetwork();
    
  SimEntity * getSimEntityForID(const size_t);
    
  void newMessage(const Simulation::SimulationEvent &e) override;

  void signalEscapeDetected(const Escape&) override;

  void signalJobFinished(int runID, int startSST) override;

  void printResultsToFile();

  juce::ThreadPool * pool;
    
  Simulation * simul;
  
  CRNSimulation crn;

  //juce::Array<Escape> pendingEscapes;
  juce::CriticalSection lock;

  StudyParameters studyParams;

  // to store escape times during this study
  // unique escape time per run
  juce::Array<Escape> escapes;

  std::atomic<int> simuRun { 0 };
  std::atomic<int> runBeingTreated { 0 };
  std::unordered_map<int, bool> escapeDetected;  // <runID, escapeDetected>
  std::unordered_map<int, Escape> earliestEscape;  // <runID, escapeDetected>
  std::unordered_map<int, int> pendingJobs;  // <runID, nJobs>

  std::atomic<bool> simuHasFinished { false };
  std::atomic<bool> resultsWritten { false };

 



  juce::String network = "./nextwork.ens";
  juce::String outputfilename = "./firstEscapeStudy.csv";
  float precision = 1e-5; // precision up to which the steady state is determined
  float exitTimePrecision = 10; // every 'exitTimePrecision', check where the system is
  int nruns = 1;
  int startSteadyState = 0;
  bool fixedSeed = false;
  int seed = 1234;
  bool debugMode = false;
  int superRun = 0;
  // In principle not designed to perform in heterogeneous space, it will complain about it otherwise
  float dt_study = 0.1; // time step used to identify in which attraction basin the system is
  bool printDynamics2File = false;
  int cores = 1;
  

  
};
