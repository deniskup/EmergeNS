/*
  ==============================================================================

  FirstEscapeTime.h
  Created: Feb. 2026
  Author:  thkosc

  ==============================================================================
*/


#include "JuceHeader.h"
//#include "Simulation/Simulation.h"
//#include "Simulation/KineticLaw.h"
#include "FirstEscapeTimeWorker.h"


class EscapeListener
{
public:
    virtual ~EscapeListener() = default;

    virtual void escapeDetected(const Escape&) = 0;
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

  void escapeDetected(const Escape&) override;

  juce::ThreadPool * pool;
    
  Simulation * simul;
  
  CRNSimulation crn;

  juce::Array<Escape> pendingEscapes;
  juce::CriticalSection pendingEscapesLock;

  // to store escape times during this study
  // unique escape time per run
  juce::Array<float> escapeTimes;
  
  juce::String networkfile = "./nextwork.txt";
//  String outputfilename = "./firstExitStudy.txt";
  float precision = 1e-5; // precision up to which the steady state is determined
  float exitTimePrecision = 10; // every 'exitTimePrecision', check where the system is
  int nruns = 1;
  int startSteadyState = 0;
  bool fixedSeed = false;
  int seed = 1234;
  // In principle not designed to perform in heterogeneous space, it will complain about it otherwise
  float dt_study = 0.1; // time step used to identify in which attraction basin the system is
  bool printDynamics2File = false;
  int cores = 1;
  

  
};
