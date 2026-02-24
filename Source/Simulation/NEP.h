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
- reparametrization of qcurve
- calculate distance from hamilton equation of motion
- recover 2-schlogl results of gagrani and smith
- smooth start when there exists some vortex arounf fixed points
 - regarding non linear solving, IPOPT to try if I want to stick to saddle point optimisation
*/

#pragma once

#include "JuceHeader.h"
//#include <nlopt.hpp>
#include <gsl/gsl_multiroots.h>
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
  Trigger * start_heteroclinic_study;
  bool heteroclinic_study = false;
  EnumParameter* sst_stable;
  EnumParameter* sst_saddle;
  IntParameter * Niterations;
  IntParameter * nPoints;
  FloatParameter * cutoffFreq;
  FloatParameter * maxcutoffFreq;
  FloatParameter * action_threshold ;
  FloatParameter * stepDescentInitVal;
  FloatParameter * timescale_factor;
  BoolParameter * maxPrinting;

  Trigger * debug;


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
  
    
  //void newMessage(const Simulation::SimulationEvent &e) override;
  
  //void newMessage(const ContainerAsyncEvent &e) override;
  
  
  void checkGradH();
  void checkGradH2();
  
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
  

  void testinitConcentrationCurve();
  void initConcentrationCurve(bool);
  
  void writeDescentToFile();
  
  void filterConcentrationTrajectory();
  
  void updateDescentParams();
  
  bool descentShouldUpdateParams(double);
  
  bool descentShouldContinue(int);
    
  LiftTrajectoryOptResults liftCurveToTrajectoryWithGSL(Curve&);

  //LiftTrajectoryOptResults liftCurveToTrajectoryWithNLOPT_old();
  
  void updateOptimalConcentrationCurve_old(const Array<StateVec> popt, const Array<double> deltaTopt);
  void updateOptimalConcentrationCurve(Curve &, double);

  double calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t);
  
  //double backTrackingMethodForStepSize(const Curve& c, const Curve& deltac);
  double backTrackingMethodForStepSize(const Curve& c);
  
  //filtering
  void applyButterworthFilter(juce::Array<double>&, std::vector<juce::dsp::IIR::Filter<double>>&);
  //vector<juce::dsp::IIR::Filter<double>> makeFilters(ReferenceCountedArray<IIRCoefficients>);
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

  
  // sample rate, calculated from current qcurve
  double sampleRate;
  
  // #para
  double stepDescentThreshold = 1e-4;
  double stepDescent;
  
  // for filtering
  //MultiButterworthLowPass filter;

  // for printing history to file
  Array<double> actionDescent;
  Array<Trajectory> trajDescent; // keep track of descent history in (q ; p) space
  Array<Trajectory> dAdqDescent; // keep track of gradient history
  Array<Trajectory> dAdqDescent_filt; // keep track of filtered gradient history
  Array<Array<double>> ham_descent; // keep track of hamiltonian evaluated along qcurve in the descent
  
  void debugNEPImplementation();

  void debugFiltering();
  
  ofstream debugfile;

  

   
};

