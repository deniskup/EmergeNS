#include "JuceHeader.h"
#include "Simulation/Simulation.h"

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
  
  int identifyAttractionBasin();
  
  void newMessage(const Simulation::SimulationEvent &e) override;

  //void newMessage(const ContainerAsyncEvent &e) override;
  
  Simulation * simul;
  
  Array<SimEntity*> entities;

  
  String networkfile;
  float precision;
  int nruns;
  String outputfilename;
  int startSteadyState;
  bool fixedSeed;
  int seed;
  
};
