// 
//  NEP.h
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//  kosc.thomas@gmail.com
// adapted from https://github.com/praful12/Descender-for-CRN-escapes/tree/main
//
//  nlopt library (used for optimizations) need to be installed
// Must modify the .jucer file to add :
// path to header files of nlopt
// -lnlopt to link to libraries
// TODO : modify

/*
- update read me for compilation with nlopt
- reparametrization of qcurve
- calculate distance from hamilton equation of motion
- recover 2-schlogl results of gagrani and smith
- smooth start when there exists some vortex arounf fixed points
*/

#pragma once

#include "JuceHeader.h"
//#include "Simulation.h"
#include "nlopt.hpp"
#include "Simulation.h"
//#include "Settings.h"

//class Simulation;
using namespace juce;

// some typedef for readability
typedef Array<double> StateVec;
typedef Array<double> PhaseSpaceVec;

// represent a curve in the concentration space
typedef Array<StateVec> Curve;
// represent a curve in the momentum space
typedef Array<StateVec> pCurve;
// represent a trajectory in the {concentration; momentum} space
typedef Array<PhaseSpaceVec> Trajectory;


// class for filtering
class MultiButterworthLowPass
{
public:
  void prepare(double sampleRate, int numEntities)
  {
    filters.clear();

    for (int i = 0; i < numEntities; ++i)
    {
      auto* f = new juce::dsp::IIR::Filter<double>();
      //juce::dsp::IIR::Filter<double> f;
      //cout << "sample rate = " << sampleRate << endl;
      //cout << "cutoff freq = " << cutoffHz << endl;
      //cout << cutoffHz << " < " << sampleRate/2.  << " ?" << endl;
      auto coeffs = juce::dsp::IIR::Coefficients<double>::makeLowPass(sampleRate, cutoffHz);
      f->coefficients = coeffs;
      filters.add(std::move(f));
    }
  }

  void process(juce::Array<juce::Array<double>>& data) // first dim = nPoints, inner dim = nentities
  {
    if (data.size()==0)
      return;
    
    // should add protection if nqyist condition not satisfied,
    // i.e. cutoffFreq < sampleRate / 2
    
    // retrieve number of entities
    const int np = static_cast<int>(data.size());
    const int numEntities = static_cast<int>(data[0].size());
    
    vector<vector<double>> filtdata(np, vector<double>(numEntities, 0.));
    
    //cout << "npoints = " << nPoints << endl;
    //cout << "numEnt = " << numEntities << endl;
    
    // I'm Here, check that this is not bullshit
    for (int ient=0; ient<numEntities; ient++)
    {
      // retrieve signal along current entity index
      vector<double> signal(np, 0.);
      for (int p=0; p<np; p++)
      {
        signal[p] = data.getUnchecked(p).getUnchecked(ient);
        //signal.setUnchecked(p, data.getUnchecked(p).getUnchecked(ient));
      }
      
      // filtering
      for (int p=0; p<signal.size(); p++)
      {
        signal[p] = filters[ient]->processSample(signal[p]);
      }
      
      // Réinjection
      for (int p=0; p<np; p++)
        filtdata[p][ient] = signal[p];
      
      // Modify input
      for (int p=0; p<np; p++)
      {
        data.getReference(p).setUnchecked(ient, filtdata[p][ient]);
      }
    } // end entity loop
    
    
  }

  void setCutoffFrequency(double newCutoffHz)
  {
    cutoffHz = newCutoffHz;
  }

private:
    double cutoffHz = 1.;
    juce::OwnedArray<juce::dsp::IIR::Filter<double>> filters;
};



class LiftTrajectoryOptResults
{
  public:
    LiftTrajectoryOptResults(){};
    ~LiftTrajectoryOptResults(){};
    Array<StateVec> opt_momentum;
    Array<double> opt_deltaT;
};



class NEP : public ControllableContainer, public Thread, public Simulation::AsyncSimListener, public ContainerAsyncListener

{
public:
  juce_DeclareSingleton(NEP, true);
  NEP();
  //NEP(Simulation *simul) : ControllableContainer("NEP"), Thread("NEP"), simul(simul),  nepNotifier(1000) {};
  //NEP(Simulation *simul);

  NEP(var data); // import from JSON
  ~NEP();
  
  Simulation * simul;
  
  // adjustable parameters
  Trigger * startDescent;
  Trigger * start_heteroclinic_study;
  bool heteroclinic_study = false;
  EnumParameter* sst_stable;
  EnumParameter* sst_saddle;
  IntParameter * Niterations;
  IntParameter * nPoints;
  FloatParameter * cutoffFreq;
  FloatParameter * action_threshold ;
  FloatParameter * timescale_factor;


  // update steady state list when updateParams is calle din SImulation
  void updateSteadyStateList();
  
  
  // methods called when container is modified
  void onContainerParameterChanged(Parameter* p) override;
  void onContainerTriggerTriggered(Trigger* t) override;
  void onChildContainerRemoved(ControllableContainer*) override;
  
  
  void reset();
  void run() override; // thread function
  
  void stop();
  
  double evalHamiltonian(const StateVec q, const StateVec p);
  StateVec evalHamiltonianGradientWithP(const StateVec q, const StateVec p);
  StateVec evalHamiltonianGradientWithQ(const StateVec q, const StateVec p);
  
  //var getJSONData() override;

  void loadJSONData(var data, bool createIfNotThere = false) override;
  
    
  void newMessage(const Simulation::SimulationEvent &e) override;
  
  void newMessage(const ContainerAsyncEvent &e) override;
  
  
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
  

  void initConcentrationCurve();
  
  void writeDescentToFile();
  
  void filterConcentrationTrajectory();
  
  void updateDescentParams();
  
  bool descentShouldUpdateParams(double);

  LiftTrajectoryOptResults liftCurveToTrajectory();
  
  void updateOptimalConcentrationCurve(const Array<StateVec> popt, const Array<double> deltaTopt);

  double calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t);
  
  double backTrackingMethodForStepSize(const Curve& c, const Curve& deltac);
  
  void nextStepHamiltonEoM(StateVec& q, StateVec& p, double dt, const bool forward, bool & shouldStop, Trajectory&);
  
  pair<Trajectory, Trajectory>  integrateHamiltonEquations(StateVec, StateVec);
  
  void heteroclinicStudy();
  
  // global variable describing the state of the descent
  Curve qcurve;
  pCurve pcurve;
  double length_qcurve = 0.;
  Array<double> times;
  double action;
  double metric = 1.; // distance from hamilton's equation of motion
  
  // sample rate, calculated from current qcurve
  double sampleRate;
  
  // #para
  double deltaActionth = 1e-4;
  double stepDescentThreshold = 1e-4;
  double stepDescent = 0.1;
  
  // for filtering
  MultiButterworthLowPass filter;

  // for printing history to file
  Array<double> actionDescent;
  Array<Trajectory> trajDescent; // keep track of descent history in (q ; p) space
  
  
  
  
  

   
};

