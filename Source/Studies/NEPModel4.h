/*
  ==============================================================================

  NEPModel4.h
  Created: Oct. 2026
  Author:  thkosc kosc.thomas@gmail.com

  ==============================================================================
*/
#pragma once

#include "JuceHeader.h"
#include "Simulation/Simulation.h"
#include "Simulation/NEP.h"
#include "Simulation/SteadyStates.h"



struct ThermoKinPair
{
  double deltaG;
  double barr;
};

struct CycleFreeEnergies
{
  double e2 = 0.;
  double e4 = 0.;
  double e5 = 0.;
};

struct Model4SteadyState
{
  SteadyState steadyState;
  double barr = 0.;
  double deltaG = 0.;
  int simID = 0;
};


class NEPModel4 : public NEP::AsyncNEPListener,
                    public Simulation::AsyncSimListener
{
public:
  juce_DeclareSingleton(NEPModel4, true);
  NEPModel4();
  ~NEPModel4();
    
  juce::Array<double> string2array(juce::String str);

  void setConfig(std::map<juce::String, juce::String>);

  void initdGBarrPairsFromCSV();
  
  void startStudy();

  void finishStudy();

  void update_dGbarr();

  CycleFreeEnergies solveFreeEnergies(const double&);

  void requestSteadyStateCalculation();

  void proceedToNext_dGbarr();

  std::pair<int, int> arrangeSteadyStates(bool&);

  void writeCustomIC(const bool);

  void launchOneGDA();

  void retrieveSteadyStates();

  void saveToMetadata(const bool&);

  void saveSteadyStatesToFile();

  void updateInternalParameters();

    
private:
    
  void newMessage(const NEP::NEPEvent &e) override;

  void newMessage(const Simulation::SimulationEvent &e) override;

    
  Simulation * simul;

  enum StudyType
  {
    STEADYSTATES,
    NEP1PATCH,
    NONE
  };

  StudyType studytype = NONE;
  
  bool initializationOK = true;

  juce::Array<double> deltaG;
  juce::Array<double> barr;
  juce::Array<ThermoKinPair> dGbarrpairs;
  int nIterations = 10;
  int nPoints = 10;
  double dtau = 1.;
  double alpha = 1.;
  bool detectConvergence = false;
  int checkpoints = 1000;
  double action_threshold = 1e-7;
  std::string outputdir = "./gda";
  juce::String msolvePath = "";

  juce::Array<Model4SteadyState> steadyStates;
  
  //juce::Array<SchloglSteadyState> stableSteadyStates;
  //juce::Array<SchloglSteadyState> saddleSteadyStates;

  // variables related to real time state of the study
  double current_dg;
  double current_barr;
  int simID = 0;
  bool fromA2B = true; // NEP from A-A to B-B or reverse
  bool nepHasError = false;


  std::string outputfile = "";
  std::string logfilename = "";
  std::string metadatafile = "";
  juce::String file_pairs_dGbarr = "";

  ofstream logerrorfile;
  ofstream ofs_metadata;


  Eigen::MatrixXd cycleMatrix;

  juce::CriticalSection lock;

};
