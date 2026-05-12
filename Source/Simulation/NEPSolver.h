// 
//  NEPSolver.h
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//  kosc.thomas@gmail.com
//


#pragma once

#include "JuceHeader.h"
#include "NEPHelper.h"


using namespace std;



class NEPSolver
{
public:
  NEPSolver();
  NEPSolver(const CRNSnapshot & _crn)
  {
    crn = _crn;
  };
  ~NEPSolver();
  
  void setReactionNetwork(CRNSnapshot _crn){crn = _crn;};
    
  double evalHamiltonian(const StateVec q, const StateVec p);
  
  StateVec evalHamiltonianGradientWithP(const StateVec q, const StateVec p);
  
  juce::dsp::Matrix<double> evalHamiltonianHessianWithP(const StateVec q, const StateVec p);
  
  StateVec evalHamiltonianGradientWithQ(const StateVec q, const StateVec p);
  
  juce::Array<double> calculateAction(const Curve& qc, const Curve& pc, const juce::Array<double>& t);
  
  void nextStepHamiltonEoM(StateVec& q, StateVec& p, double dt, const bool forward, bool & shouldStop, Trajectory&);
  
private:
  
  CRNSnapshot crn;
  
};


