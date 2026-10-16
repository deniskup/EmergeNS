/*
  ==============================================================================

  FirstEscapeTime.h
  Created: Oct. 2026
  Author:  thkosc kosc.thomas@gmail.com

  ==============================================================================
*/
#pragma once

#include "JuceHeader.h"
#include "Simulation/Simulation.h"
#include "Simulation/NEP.h"
#include "Simulation/SteadyStates.h"



struct thetakdPair
{
  double theta;
  double kd;
};

struct SchloglSteadyState
{
  double X1;
  double X2;
  int stabilityOrder; // number of positive eigenvalue of jacobian. 0 mean stable, 1 means saddle point, etc.
  int positionInList; // position in the list of steady states
};


class NEPSchlogl : public NEP::AsyncNEPListener,
                    public Simulation::AsyncSimListener
                    //public SteadyStateslist::AsyncSstListener
{
public:
  juce_DeclareSingleton(NEPSchlogl, true);
  NEPSchlogl();
  ~NEPSchlogl();
    
  void setConfig(std::map<juce::String, juce::String>);
  
  void startStudy();

  void finishStudy();

  void updateThetaKd();

  void requestSteadyStateCalculation();

  void proceedToNextThetaKd();

  bool arrangeSteadyStates();

  void writeCustomIC(const bool);

  void launchOneGDA();

  void saveToMetadata(const bool&);

  void updateInternalParameters();

    
private:
    
  void newMessage(const NEP::NEPEvent &e) override;

  //void newMessage(const SteadyStateslist::SteadyStateEvent &e) override;
  void newMessage(const Simulation::SimulationEvent &e) override;

    
  Simulation * simul;
  
  bool initializationOK = true;

  juce::Array<double> theta;
  juce::Array<double> kd;
  juce::Array<thetakdPair> thetakdpairs;
  int nIterations = 10;
  int nPoints = 10;
  double dtau = 1.;
  double alpha = 1.;
  bool detectConvergence = false;
  int checkpoints = 1000;
  double action_threshold = 1e-7;
  juce::Array<SchloglSteadyState> stableSteadyStates;
  juce::Array<SchloglSteadyState> saddleSteadyStates;

  juce::CriticalSection lock;

  double current_theta;
  double current_kd;

  int simID = 0;
  bool low2high = true; // NEP from low-low to high-high or reverse

  std::string outputfile = "";

  ofstream logerrorfile;
  ofstream ofs_metadata;

  bool nepHasError = false;


  
};
