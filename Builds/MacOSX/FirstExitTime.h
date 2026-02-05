#include "JuceHeader.h"
#include "Simulation/Simulation.h"

class FirstExitTime : public Simulation::AsyncSimListener//,
                     // public ContainerAsyncListener
{
public:
  juce_DeclareSingleton(FirstExitTime, true);
  FirstExitTime();
  ~FirstExitTime();
  
  void setSimulationConfig(std::map<String, String>);
  
  void startStudy();
  
  void newMessage(const Simulation::SimulationEvent &e) override;

  //void newMessage(const ContainerAsyncEvent &e) override;

  
  String networkfile;
  float precision;
  int nruns;
  String outputfilename;
  int startSteadyState;
  bool fixedSeed;
  int seed;
  
};
