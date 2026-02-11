#include "JuceHeader.h"
//#include "Simulation/Simulation.h"
//#include "Simulation/KineticLaw.h"
#include "FirstExitTimeWorker.h"

class FirstExitTime : public Simulation::AsyncSimListener
{
public:
  juce_DeclareSingleton(FirstExitTime, true);
  FirstExitTime();
  ~FirstExitTime();
    
  void setSimulationConfig(std::map<String, String>);
  
  void startStudy();
    
private:
  
  int identifyAttractionBasin(ConcentrationGrid &, float);
    
  SimEntity * getSimEntityForID(const size_t);
  
  //void printResultsToFile();
  
  void newMessage(const Simulation::SimulationEvent &e) override;
  
  FirstExitTimeWorker * worker;
  
  Simulation * simul;
  


  // to store escape times during this study
  Array<float> escapeTimes;
  
  String networkfile = "./nextwork.txt";
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
  

  
};
