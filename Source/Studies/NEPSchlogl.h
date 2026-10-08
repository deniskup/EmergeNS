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


struct thetakdPair
{
  double theta;
  double kd;
};


class NEPSchlogl : public Simulation::AsyncSimListener,
                    public NEP::AsyncNEPListener,
                    public SteadyStateslist::AsyncSstListener
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

  void launchOneGDA();
    
private:
    
  void newMessage(const NEP::NEPEvent &e) override;

  //void newMessage(const ContainerAsyncEvent &e) override;

  void newMessage(const SteadyStateslist::SteadyStateEvent &e) override;

    
  Simulation * simul;
  
  bool initializationOK = true;

  juce::Array<double> theta;
  juce::Array<double> kd;
  juce::Array<thetakdPair> thetakdpairs;
  int nIterations = 10;
  int nPoints = 10;

  juce::CriticalSection lock;

  
};
