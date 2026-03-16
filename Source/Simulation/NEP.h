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
#include <gsl/gsl_multiroots.h>
#include <gsl/gsl_blas.h>
#include <random>
#include "KineticLaw.h"

class Simulation;

using namespace std;

//class Simulation;
//class Simulation::SimulationEvent;
//class Simulation::AsyncSimListener;

using namespace juce;

// some typedef for readability
typedef Array<double> StateVec;
typedef Array<double> PhaseSpaceVec;
//typedef Array<Array<double>> Matrix;

// represent a curve in the concentration space
typedef Array<StateVec> Curve;
// represent a curve in the momentum space
typedef Array<StateVec> pCurve;
// represent a trajectory in the {concentration; momentum} space
typedef Array<PhaseSpaceVec> Trajectory;




class LiftTrajectoryOptResults
{
  public:
    LiftTrajectoryOptResults(){};
    ~LiftTrajectoryOptResults(){};
    Array<StateVec> opt_momentum;
    Array<double> opt_deltaT;
    pCurve pcurve;
    Array<double> times;
    vector<int> gslStatus;
};

class NEP;

struct EncapsVarForNLOpt {
  const Array<double>* qcenter; // current concentration point
  const Array<double>* deltaq; // current concentration point
  Array<double>* p; // p variable to pass to t optimisation
  NEP * nep; // nep class for hamiltonian class
  double t_opt; // t variable that optimizes the lagrangian
  //Array<double> p_opt; // t variable that optimizes the lagrangian
};


struct EncapsVarForGSL {
  Array<double> qcenter; // current concentration point
  Array<double> deltaq; // current concentration point
  NEP * nep; // nep class for hamiltonian calculations
  double epsilon = 1.;
  Array<double> pnorm;
  Array<double> equation_norm;
  dsp::Matrix<double> B{0, 0}; // elements lines are orthogonal basis of deltaq
};




class NEP : public ControllableContainer, public Thread/*, public Simulation::AsyncSimListener, public ContainerAsyncListener*/

{
public:
  juce_DeclareSingleton(NEP, true);
  NEP();

  NEP(var data); // import from JSON
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
  IntParameter * nPoints_start;
  IntParameter * nPoints_max;
  FloatParameter * cutoffFreq;
  FloatParameter * maxcutoffFreq;
  FloatParameter * action_threshold ;
  FloatParameter * stepDescentInitVal;
  //FloatParameter * timescale_factor;
  BoolParameter * maxPrinting;
  EnumParameter* initialConditions;


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
  
  dsp::Matrix<double> evalHamiltonianHessianWithP(const StateVec q, const StateVec p);
  
  StateVec evalHamiltonianGradientWithQ(const StateVec q, const StateVec p);
  
  //var getJSONData() override;

  void loadJSONData(var data, bool createIfNotThere = false) override;
  
    
  // ASYNC
  class NEPEvent
  {
  public:
    enum Type
    {
      WILL_START,
      NEWSTEP,
    };

    NEPEvent(Type _t, NEP* _nep, int _curStep = 0, double _action = 0., double _cutofffreq = 0., int _npoints = 1, double _metric = 0.)
      : type(_t), nep(_nep), curStep(_curStep), action(_action), cutofffreq(_cutofffreq), npoints(_npoints), metric(_metric)
    {
    }

    Type type;
    NEP* nep;
    int curStep;
    double action;
    double cutofffreq;
    int npoints;
    double metric;
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
  
  dsp::Matrix<double> buildOrthogonalBasis(StateVec v);
  
  gsl_vector * initialOptimalGuess_old(const int, bool, const vector<double>, const StateVec);
  gsl_vector * initialOptimalGuess(const int, bool, const vector<double>, const StateVec);
  
  int gslMultirootSolving_old(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  int gslMultirootSolving(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  
  LiftTrajectoryOptResults findOptimalMomentumAndTime_old(const Curve&, const int n, bool);
  LiftTrajectoryOptResults findOptimalMomentumAndTime(const Curve&, const int n, bool);
    
  LiftTrajectoryOptResults liftCurveToTrajectoryWithGSL(const Curve&, bool);

  //LiftTrajectoryOptResults liftCurveToTrajectoryWithNLOPT_old();
  
  void updateOptimalConcentrationCurve_old(const Array<StateVec> popt, const Array<double> deltaTopt);
  
  void updateOptimalConcentrationCurve(Curve &, double);

  //double calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t);
  Array<double> calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t);
  
  double backTrackingMethodForStepSize(const Curve& c);
  
  //filtering
  void applyButterworthFilter(juce::Array<double>&, std::vector<juce::dsp::IIR::Filter<double>>&);
  void resampleInSpaceUniform(Array<StateVec>& signal, int);
  void resampleInTimeUniform(Array<StateVec>& signal, int);
  void lowPassFiltering(Array<StateVec>&, bool);
  
  void nextStepHamiltonEoM(StateVec& q, StateVec& p, double dt, const bool forward, bool & shouldStop, Trajectory&);
  
  pair<Trajectory, Trajectory>  integrateHamiltonEquations(StateVec, StateVec);
  
  void heteroclinicStudy();
  
  KineticLaw * kinetics; // to calculate kinetics
  
  // global variable describing the state of the descent
  Curve g_qcurve;
  pCurve g_pcurve;
  double length_qcurve = 0.;
  Array<double> g_times;
  double action;
  double metric = 1.; // distance from hamilton's equation of motion
  Array<StateVec> dAdq, dAdq_filt;

  // number of sampling points
  int nPoints;
  int nPoints_increment = 10;
  
  // decides whether concentration curve cab be update q^{i+1} = q^{i} - dA/dq
  bool canUpdateConcentrationCurve = true;
  
  // sample rate, calculated from current qcurve
  double sampleRate;
  
  // #para
  double stepDescentThreshold = 1e-4;
  double stepDescent;
  
  // normalization parameters
  double timescale_factor = 1.;
  

  // for printing history to file
  //Array<double> actionDescent;
  Array<Array<double>> actionDescent;
  Array<Trajectory> trajDescent; // keep track of descent history in (q ; p) space
  Array<Trajectory> dAdqDescent; // keep track of gradient history
  Array<Trajectory> dAdqDescent_filt; // keep track of filtered gradient history
  Array<Array<double>> ham_descent; // keep track of hamiltonian evaluated along qcurve in the descent
    
  ofstream debugfile;

  

   
};


