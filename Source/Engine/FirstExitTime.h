#include "JuceHeader.h"
#include "Simulation/Simulation.h"
#include "Simulation/KineticLaw.h"

class FirstExitTime : public Simulation::AsyncSimListener//,
                     // public ContainerAsyncListener
{
public:
  juce_DeclareSingleton(FirstExitTime, true);
  FirstExitTime();
  ~FirstExitTime();
  
  void reset();
  
  void setSimulationConfig(std::map<String, String>);
  
  void startStudy();
  
  //void setConcToSteadyState(int);
  
private:
  
  int identifyAttractionBasin(ConcentrationGrid &, float);
  
  float distanceFromSteadyState(State sst);
  
  SimEntity * getSimEntityForID(const size_t);
  
  void printResultsToFile();
  
  void newMessage(const Simulation::SimulationEvent &e) override;

  //void newMessage(const ContainerAsyncEvent &e) override;
  
  Simulation * simul;
  KineticLaw * kinetics;
  
  OwnedArray<SimEntity> entities;
  OwnedArray<SimReaction> reactions;

  // to store escape times during this study
  Array<float> escapeTimes;
  
  String networkfile = "./nextwork.txt";
  float precision = 1e-5; // precision up to which the steady state is determined
  float exitTimePrecision = 10; // every 'exitTimePrecision', check where the system is
  int superRun = 0;
  int nruns = 1;
  String outputfilename = "firstExitStudy.txt";
  int startSteadyState = 0;
  bool fixedSeed = false;
  int seed = 1234;
  int patchid = 0; // hardcoded patch in which this study takes place.
  float dt_study = 0.1; // time step used to identify in which attraction basin the system is
  // In principle not designed to perform in heterogeneous space, it will complain about it otherwise

  
};
