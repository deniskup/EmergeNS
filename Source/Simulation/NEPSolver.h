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

  //std::pair<StateVec, StateVec> GDAfg(StateVec u, StateVec v, double alpha);

  juce::Array<StateVec> GDAf1(const juce::Array<StateVec>&, const juce::Array<StateVec>&, double);

  juce::Array<StateVec> GDAf2(const juce::Array<StateVec>&, const juce::Array<StateVec>&, double);


  std::pair<Curve, Curve> GDAfromQPtoUV(const juce::Array<StateVec>& qcurve, const juce::Array<StateVec>& pcurve, double alpha);

  std::pair<Curve, Curve> GDAfromUVtoQP(const juce::Array<StateVec>& ucurve, const juce::Array<StateVec>& vcurve, double alpha);

  //double GDAlambda(StateVec u, StateVec v, double alpha, double ds);

  juce::Array<double> GDAlambdaArrayFromQP(const juce::Array<StateVec>&, const juce::Array<StateVec>&, const juce::Array<double>&, const juce::Array<StateVec>&, double, double);

  //juce::Array<double> GDAlambdaArrayFromUV(const juce::Array<StateVec>& ucurve, const juce::Array<StateVec>& vcurve, double alpha, double ds);

  void GDAupdateUCurve(juce::Array<StateVec>&, const juce::Array<StateVec>&, const juce::Array<StateVec>&, const juce::Array<double>&, const juce::Array<StateVec>&, double, double, double, const StateVec&);

  void GDAupdateVCurve(juce::Array<StateVec>&, const juce::Array<StateVec>&, const juce::Array<StateVec>&, const juce::Array<double>&, const juce::Array<StateVec>&, double, double, double, const StateVec&);

  void GDAupdateUCurveSecondOrder(juce::Array<StateVec>&, const juce::Array<StateVec>&, const juce::Array<StateVec>&, const juce::Array<double>&, const juce::Array<StateVec>&, double, double, double, const StateVec&);

  void GDAupdateVCurveSecondOrder(juce::Array<StateVec>&, const juce::Array<StateVec>&, const juce::Array<StateVec>&, const juce::Array<double>&, const juce::Array<StateVec>&, double, double, double, const StateVec&);

  juce::Array<double> GDAcalculateAction(const Curve& qc, const Curve& pc, const juce::Array<double>& lambdaArray, bool forceStationnarity = false);
  
  
//private:
  
  CRNSnapshot * crn;
  
};

