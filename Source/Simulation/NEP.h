// 
//  NEP.h
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//  kosc.thomas@gmail.com
// adapted from https://github.com/praful12/Descender-for-CRN-escapes/tree/main
//

/*
- update read me for compilation with gsl, indicate that user should add lib and header paths to projucer file
- better handling of verbose
- calculate distance from hamilton equation of motion
- smooth start when there exists some vortex arounf fixed points
- regarding non linear solving, IPOPT to try if wish to stick to saddle point optimisation
*/

#pragma once

#include "JuceHeader.h"
//#include <nlopt.hpp>
#include <gsl/gsl_roots.h>
#include <gsl/gsl_multiroots.h>
#include <gsl/gsl_blas.h>
#include "gsl/gsl_multimin.h"
#include <random>
#include "KineticLaw.h"

class Simulation;

using namespace std;

//class Simulation;
//class Simulation::SimulationEvent;
//class Simulation::AsyncSimListener;

//using namespace juce;

// some typedef for readability
typedef juce::Array<double> StateVec;
typedef juce::Array<double> PhaseSpaceVec;
//typedef juce::Array<juce::Array<double>> Matrix;

// represent a curve in the concentration space
typedef juce::Array<StateVec> Curve;
// represent a curve in the momentum space
typedef juce::Array<StateVec> pCurve;
// represent a trajectory in the {concentration; momentum} space
typedef juce::Array<PhaseSpaceVec> Trajectory;




class LiftTrajectoryOptResults
{
  public:
    LiftTrajectoryOptResults(){};
    ~LiftTrajectoryOptResults(){};
    juce::Array<StateVec> opt_momentum;
    juce::Array<double> opt_deltaT;
    pCurve pcurve;
    Array<double> times;
    Array<int> gslStatus;
    Array<int> collinearity;
    juce::Array<double> residuals_H;
    juce::Array<juce::Array<double>> residuals_p;
};

class NEP;

struct EncapsVarForNLOpt {
  const juce::Array<double>* qcenter; // current concentration point
  const juce::Array<double>* deltaq; // current concentration point
  juce::Array<double>* p; // p variable to pass to t optimisation
  NEP * nep; // nep class for hamiltonian class
  double t_opt; // t variable that optimizes the lagrangian
  //juce::Array<double> p_opt; // t variable that optimizes the lagrangian
};




struct EncapsVarForGSL {
  juce::Array<double> qcenter; // current concentration point
  juce::Array<double> deltaq; // current concentration point
  NEP * nep; // nep class for hamiltonian calculations
  double epsilon = 1.;
  Array<double> pnorm;
  Array<double> equation_norm;
  dsp::Matrix<double> B{0, 0}; // elements lines are orthogonal basis of deltaq
  //double mu;
  double s;
};

struct EncapsVarForGSL_MU {
  Array<double> q; // current concentration point
  Array<double> p; // current concentration point
  Array<double> dq;
  double dq_norm2;
  NEP * nep; // nep class for hamiltonian calculations
};




class NEP : public ControllableContainer, public juce::Thread/*, public Simulation::AsyncSimListener, public ContainerAsyncListener*/

{
public:
  juce_DeclareSingleton(NEP, true);
  NEP();

  NEP(juce::var data); // import from JSON
  ~NEP();
  
  Simulation * simul;
  
  enum NEPState
  {
    Descending,
    Idle
  };
  
  const char* toString(NEPState s)
  {
    switch (s)
    {
      case Descending: return "Descending";
      case Idle:       return "Idle";
      default:         return "Unknown";
    }
  }
  
  NEPState state = Idle;
  
  // adjustable parameters
  Trigger * startDescent;
  Trigger * stopDescent;
  Trigger * start_heteroclinic_study;
  Trigger * test;
  bool heteroclinic_study = false;
  EnumParameter* sst_stable;
  EnumParameter* sst_saddle;
  IntParameter * Niterations;
  IntParameter * nPoints_UI;
  IntParameter * nPoints_max;
  FloatParameter * cutoffFreq;
  FloatParameter * maxcutoffFreq;
  FloatParameter * action_threshold ;
  FloatParameter * stepDescentInitVal;
  //FloatParameter * timescale_factor;
  BoolParameter * maxPrinting;
  EnumParameter* initialConditions;
  EnumParameter* solverType;


  // update steady state list when updateParams is calle din SImulation
  void updateSteadyStateList();
  
  
  // methods called when container is modified
  void onContainerParameterChanged(Parameter* p) override;
  void onContainerTriggerTriggered(Trigger* t) override;
  void onChildContainerRemoved(ControllableContainer*) override;
  
  
  void reset();
  void stop();
  void run() override; // thread function

  
  
  
  double evalHamiltonian(const StateVec q, const StateVec p);
  
  StateVec evalHamiltonianGradientWithP(const StateVec q, const StateVec p);
  
  juce::dsp::Matrix<double> evalHamiltonianHessianWithP(const StateVec q, const StateVec p);
  
  StateVec evalHamiltonianGradientWithQ(const StateVec q, const StateVec p);
  
  //var getJSONData() override;

  void loadJSONData(juce::var data, bool createIfNotThere = false) override;
  
    
  // ASYNC
  class NEPEvent
  {
  public:
    enum Type
    {
      WILL_START,
      NEWSTEP,
    };

    NEPEvent(Type _t, NEP* _nep, int _curStep = 0, double _action = 0., double _cutofffreq = 0., int _npoints = 1, double _metric = 0., double _convergenceFraction = 0.)
      : type(_t), nep(_nep), curStep(_curStep), action(_action), cutofffreq(_cutofffreq), npoints(_npoints), metric(_metric), convergenceFraction(_convergenceFraction)
    {
    }

    Type type;
    NEP* nep;
    int curStep;
    double action;
    double cutofffreq;
    int npoints;
    double metric;
    double convergenceFraction;
  };
  
  QueuedNotifier<NEPEvent> nepNotifier;
  std::set<void*> debugKnownListeners;
  typedef QueuedNotifier<NEPEvent>::Listener AsyncNEPListener;

  void addAsyncNEPListener(AsyncNEPListener* newListener) {nepNotifier.addListener(newListener); }
  void addAsyncCoalescedNEPListener(AsyncNEPListener* newListener) { nepNotifier.addAsyncCoalescedListener(newListener);}
  void removeAsyncNEPListener(AsyncNEPListener* listener) {nepNotifier.removeListener(listener);}


  
private:
  
  void setTimeNormalizationFactor();

  void initConcentrationCurve();
  
  void writeDescentToFile();
  
  void filterConcentrationTrajectory();
  
  void updateDescentParams();
  
  bool descentShouldUpdateParams(double);
  
  bool descentShouldContinue(int);
  
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
  
  void updateOptimalConcentrationCurve_old(const juce::Array<StateVec> popt, const juce::Array<double> deltaTopt);
  
  //void updateOptimalConcentrationCurve(Curve &, double);
  bool updateOptimalConcentrationCurve(Curve &, double);

  //double calculateAction(const Curve& qc, const Curve& pc, const juce::Array<double>& t);
  juce::Array<double> calculateAction(const Curve& qc, const Curve& pc, const juce::Array<double>& t);
  
  double backTrackingMethodForStepSize(const Curve& c);
  
  //filtering
  void applyButterworthFilter(juce::Array<double>&, std::vector<juce::dsp::IIR::Filter<double>>&);
  void resampleInSpaceUniform(Array<StateVec>& signal, int);
  void resampleInTimeUniform(Array<StateVec>& signal, int);
  //void lowPassFiltering(Array<StateVec>&, bool);
  
  void nextStepHamiltonEoM(StateVec& q, StateVec& p, double dt, const bool forward, bool & shouldStop, Trajectory&);
  
  pair<Trajectory, Trajectory>  integrateHamiltonEquations(StateVec, StateVec);
  
  void heteroclinicStudy();
  
  void debuggingFunction();
  
  KineticLaw * kinetics; // to calculate kinetics
  
  // global variable describing the state of the descent
  Curve g_qcurve;
  pCurve g_pcurve;
  double length_qcurve = 0.;
  juce::Array<double> g_times;
  double action;
  double metric = 1.; // distance from hamilton's equation of motion
  juce::Array<StateVec> dAdq, dAdq_filt;

  // number of sampling points
  int nPoints;
  int nPoints_increment = 10;
  
  // decides whether concentration curve cab be update q^{i+1} = q^{i} - dA/dq
  bool canUpdateConcentrationCurve = true;
  
  // sample rate, calculated from current qcurve
  double sampleRate;
  
  // #para
  double stepDescentThreshold = 1e-6;
  double stepDescent;
  double stepDescentInit_dynamic;
  double tolerance_mu_init = 1e-5;
  double tolerance_mu_min = 1e-10;
  double tolerance_mu;
  
  // normalization parameters
  double timescale_factor = 1.;
  

  // for printing history to file
  //Array<double> actionDescent;
  Array<Array<double>> actionDescent;
  Array<Trajectory> trajDescent; // keep track of descent history in (q ; p) space
  Array<Trajectory> dAdqDescent; // keep track of gradient history
  Array<Trajectory> dAdqDescent_filt; // keep track of filtered gradient history
  Array<Array<int>> gslStatus_descent;
  Array<Array<int>> collinearityStatus_descent;
  juce::Array<juce::Array<double>> residuals_H_descent;
  juce::Array<Trajectory> residuals_p_descent;
    
  ofstream debugfile;

  

   
};


