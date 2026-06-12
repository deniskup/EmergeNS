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
  //NEPSolver();
  NEPSolver(CRNSnapshot & _crn)
  {
    crn = &_crn;
  };
  ~NEPSolver();
  
  void setReactionNetwork(CRNSnapshot& _crn){crn = &_crn;};
    
  double evalHamiltonian(const StateVec q, const StateVec p, bool useChangeOfVariable = false);
  
  StateVec evalHamiltonianGradientWithP(const StateVec q, const StateVec p);

  StateVec evalUtimesHamiltonianGradientWithU(const StateVec q, const StateVec u);

  juce::dsp::Matrix<double>  evalHamiltonianHessianWithU(const StateVec q, const StateVec u);

  StateVec evalHamiltonianGradientWithU(const StateVec q, const StateVec u);
  
  juce::dsp::Matrix<double> evalHamiltonianHessianWithP(const StateVec q, const StateVec p);
  
  StateVec evalHamiltonianGradientWithQ(const StateVec q, const StateVec p);
  
  juce::Array<double> calculateAction(const Curve& qc, const Curve& pc, const juce::Array<double>& t);
  
  void nextStepHamiltonEoM(StateVec& q, StateVec& p, StateVec& qstart, StateVec& pstart, double dt, const bool forward, bool & shouldStop, Trajectory&);

  void setCRNNormalization(double norm)
  {
    if (norm <=0.)
      norm = 1.;
    crn->timescale_factor *= norm;
  }
  
//private:
  
  CRNSnapshot * crn;
  
};


