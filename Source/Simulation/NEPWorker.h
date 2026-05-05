// 
//  NEPWorker.h
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//  kosc.thomas@gmail.com
//


#pragma once

#include "JuceHeader.h"
#include "NEPSolver.h"
#include "NEPHelper.h"
//#include <nlopt.hpp>
#include <gsl/gsl_roots.h>
#include <gsl/gsl_multiroots.h>
#include <gsl/gsl_blas.h>
#include "gsl/gsl_multimin.h"

#include <Eigen/Dense>

using namespace std;


struct EncapsVarForNLOpt {
  const juce::Array<double>* q; // current concentration point
  const juce::Array<double>* dq;
  juce::Array<double>* p; // p variable to pass to t optimisation
  double t_opt; // t variable that optimizes the lagrangian
  //juce::Array<double> p_opt; // t variable that optimizes the lagrangian
};


struct EncapsVarForGSL {
  juce::Array<double> q; // current concentration point
  juce::Array<double> dq;
  double epsilon = 1.;
  juce::Array<double> pnorm;
  juce::Array<double> equation_norm;
  juce::dsp::Matrix<double> B{0, 0}; // elements lines are orthogonal basis of deltaq
  //double mu;
  double s;
  int n;
  StateVec pstar_prev;
  double dt_prev;
  NEPSolver * solver;
};


struct EncapsVarForGSL_MU {
  juce::Array<double> q; // current concentration point
  juce::Array<double> p;
  juce::Array<double> dq;
  double dq_norm2;
  NEPSolver * solver;
};



class NEPWorker : public juce::ThreadPoolJob
{
public:
  NEPWorker(const CRNSnapshot & _crn, const EncapsVarForGSL _ev,  NLSresults & _results, double _tolerance, int _solverType, int _index, bool _maxPrintingAllowed)
  : juce::ThreadPoolJob("NEPWorker"), crn(_crn), ev(_ev), results(_results), tolerance(_tolerance), nlsolverType(_solverType), idx(_index), maxPrintingAllowed(_maxPrintingAllowed)
  {
    solver = new NEPSolver(crn);
  }

  
  JobStatus runJob() override;
  
private:
      
  void correctMomentumDirectionIfFollowingWrongBranch(gsl_vector&, StateVec, StateVec);
  
  //int gslMultirootSolving_brutforce(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  int gslMultirootSolving(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  int gslMultirootSolving_opt(gsl_multiroot_fdfsolver*, gsl_root_fdfsolver*, gsl_multiroot_function_fdf &, gsl_function_fdf&, EncapsVarForGSL &, EncapsVarForGSL_MU &);
  int solveForMomentumAtFixedMu(gsl_multimin_fdfminimizer *, EncapsVarForGSL&, double);
  int gslMultirootSolving_LF(gsl_multimin_fdfminimizer*, gsl_root_fdfsolver*, gsl_multimin_function_fdf &, gsl_function_fdf&, EncapsVarForGSL &, EncapsVarForGSL_MU &);
  
  
  NLSresults findOptimalMomentumAndTime();
  
  //LiftTrajectoryOptResults liftCurveToTrajectoryWithGSL(const Curve&, bool);
  
  NEPSolver * solver;
  
  const CRNSnapshot crn;
  
  EncapsVarForGSL ev;
  
  NLSresults & results;

  int idx;
  
  int nlsolverType;
  
  bool maxPrintingAllowed;
  
  double tolerance;
};

/*

{
public:
  NEP();

  NEP(juce::var data); // import from JSON
  ~NEP();

  juce::dsp::Matrix<double> buildOrthogonalBasis(StateVec v);
  
  gsl_vector * initialOptimalGuess_brutforce(const int, bool, const vector<double>, const StateVec);
  gsl_vector * initialOptimalGuess(const int, bool, const vector<double>, const StateVec);
  
  int gslMultirootSolving_brutforce(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  void correctMomentumDirectionIfFollowingWrongBranch(gsl_vector&, StateVec, StateVec);
  int gslMultirootSolving(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  int gslMultirootSolving_opt(gsl_multiroot_fdfsolver*, gsl_root_fdfsolver*, gsl_multiroot_function_fdf &, gsl_function_fdf&, EncapsVarForGSL &, EncapsVarForGSL_MU &);
  
  int solveForMomentumAtFixedMu(gsl_multimin_fdfminimizer *, EncapsVarForGSL&, double);
  int gslMultirootSolving_LF(gsl_multimin_fdfminimizer*, gsl_root_fdfsolver*, gsl_multimin_function_fdf &, gsl_function_fdf&, EncapsVarForGSL &, EncapsVarForGSL_MU &);
  
  LiftTrajectoryOptResults findOptimalMomentumAndTime_brutforce(const Curve&, const int n, bool);
  LiftTrajectoryOptResults findOptimalMomentumAndTime(const Curve&, const int n, bool);
  LiftTrajectoryOptResults findOptimalMomentumAndTime_opt(const Curve&, const int n, bool);
  LiftTrajectoryOptResults findOptimalMomentumAndTime_LF(const Curve&, const int n, bool);
    
  LiftTrajectoryOptResults liftCurveToTrajectoryWithGSL(const Curve&, bool);

  //LiftTrajectoryOptResults liftCurveToTrajectoryWithNLOPT_old();

   
};

*/
