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
//#include <gsl/gsl_roots.h>
//#include <gsl/gsl_multiroots.h>
//#include <gsl/gsl_blas.h>
//#include "gsl/gsl_multimin.h"

#include <Eigen/Dense>

using namespace std;








class NEPWorker : public juce::ThreadPoolJob
{
public:
  NEPWorker(CRNSnapshot _crn, const EncapsVarForGSL _ev,  NLSresults & _results, double _tolerance, int _solverType, int _index, bool _maxPrintingAllowed, bool _useChangeOfVariable)
  : juce::ThreadPoolJob("NEPWorker"), crn(_crn), ev(_ev), results(_results), tolerance(_tolerance), 
  nlsolverType(_solverType), idx(_index), maxPrintingAllowed(_maxPrintingAllowed), useChangeOfVariable(_useChangeOfVariable)
  {
    solver = new NEPSolver(crn);
  }

  
  JobStatus runJob() override;
  
private:
      
  //void correctMomentumDirectionIfFollowingWrongBranch(gsl_vector&, StateVec, StateVec);
  
  //int gslMultirootSolving_brutforce(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  
  //int gslMultirootSolving(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  
  double smoothUpdateOnMu(StateVec, StateVec, double);

  
  //bool solveForMomentumAtFixedMu_opt(gsl_multiroot_fdfsolver *, EncapsVarForGSL&, double, int);
  //int gslMultirootSolving_opt(gsl_multiroot_fdfsolver*, gsl_root_fdfsolver*, gsl_multiroot_function_fdf &, gsl_function_fdf&, EncapsVarForGSL &, EncapsVarForGSL_MU &);
  
  //bool solveForMomentumAtFixedMu_LF(gsl_multimin_fdfminimizer *, EncapsVarForGSL&, double, int);
  //int gslMultirootSolving_LF(gsl_multimin_fdfminimizer*, gsl_root_fdfsolver*, gsl_multimin_function_fdf &, gsl_function_fdf&, EncapsVarForGSL &, EncapsVarForGSL_MU &);
  
  
  NLSresults findOptimalMomentumAndTime();
  
  //LiftTrajectoryOptResults liftCurveToTrajectoryWithGSL(const Curve&, bool);
  
  NEPSolver * solver;
  
  CRNSnapshot crn;
  
  EncapsVarForGSL ev;
  
  NLSresults & results;

  int idx;
  
  int nlsolverType;
  
  bool maxPrintingAllowed;
  
  double tolerance;
  
  int maxiteration = 100;

  bool useChangeOfVariable;
};

