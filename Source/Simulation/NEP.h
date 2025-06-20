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
    const int nPoints = static_cast<int>(data.size());
    const int numEntities = static_cast<int>(data[0].size());
    
    vector<vector<double>> filtdata(nPoints, vector<double>(numEntities, 0.));
    
    //cout << "npoints = " << nPoints << endl;
    //cout << "numEnt = " << numEntities << endl;
    
    // I'm Here, check that this is not bullshit
    for (int ient=0; ient<numEntities; ient++)
    {
      // retrieve signal along current entity index
      vector<double> signal(nPoints, 0.);
      for (int p=0; p<nPoints; p++)
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
      for (int p=0; p<nPoints; p++)
        filtdata[p][ient] = signal[p];
      
      // Modify input
      for (int p=0; p<nPoints; p++)
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
  
  
  
  void loadJSONData(var data, bool createIfNotThere = false) override;
  var getJSONData(bool includeNonOverriden = true) override;
  
  
   class NEPListener
   {
   public:
   virtual ~NEPListener() {}
   virtual void updateNEPUI(NEP *){};
   };
   
   
   ListenerList<NEPListener> listeners;
   void addNEPListener(NEPListener *newListener) { listeners.add(newListener); }
   void removeNEPListener(NEPListener *listener) { listeners.remove(listener); }
  
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
      UPDATEPARAMS,
      WILL_START,
      STARTED,
      NEWSTEP,
      FINISHED,
    };

    NEPEvent(Type _t, NEP* _nep, int _curStep = 0, double _action = 0.)
      : type(_t), nep(_nep), curStep(_curStep), action(_action)
    {
    }

    Type type;
    NEP* nep;
    int curStep;
    double action;
  };
  
  QueuedNotifier<NEPEvent> nepNotifier;
  typedef QueuedNotifier<NEPEvent>::Listener AsyncNEPListener;

  void addAsyncNEPListener(AsyncNEPListener* newListener) { nepNotifier.addListener(newListener); }
  void addAsyncCoalescedNEPListener(AsyncNEPListener* newListener) { nepNotifier.addAsyncCoalescedListener(newListener); }
  void removeAsyncNEPListener(AsyncNEPListener* listener) { nepNotifier.removeListener(listener); }
  
/*
  QueuedNotifier<SimulationEvent> simNotifier;
  typedef QueuedNotifier<SimulationEvent>::Listener AsyncSimListener;

  void addAsyncSimulationListener(AsyncSimListener* newListener) { simNotifier.addListener(newListener); }
  void addAsyncCoalescedSimulationListener(AsyncSimListener* newListener) { simNotifier.addAsyncCoalescedListener(newListener); }
  void removeAsyncSimulationListener(AsyncSimListener* listener) { simNotifier.removeListener(listener); }
  */
/*
  // ASYNC
  class SimulationEvent
  {
  public:
    enum Type
    {
      UPDATEPARAMS,
      WILL_START,
      STARTED,
      NEWSTEP,
      FINISHED,
    };

    SimulationEvent(Type t,
      Simulation* sim,
      //int _run = 0,
      //int _patch = 0,
      int curStep = 0,
      //Array<float> entityValues = Array<float>(),
      ConcentrationGrid entityValues = {},
      Array<Colour> entityColors = Array<Colour>(),
      Array<float> PACsValues = Array<float>(),
      Array<bool> RACList = Array<bool>())
      : type(t), sim(sim), curStep(curStep), entityValues(entityValues), entityColors(entityColors), PACsValues(PACsValues), RACList(RACList)
    {
    }

    Type type;
    Simulation* sim;
    //int run;
    //int patch;
    int curStep;
    //Array<float> entityValues;
    ConcentrationGrid entityValues;
    Array<Colour> entityColors;
    Array<float> PACsValues;
    Array<bool> RACList;
    //map<PAC*, bool> RACList;
  };

  QueuedNotifier<SimulationEvent> simNotifier;
  typedef QueuedNotifier<SimulationEvent>::Listener AsyncSimListener;

  void addAsyncSimulationListener(AsyncSimListener* newListener) { simNotifier.addListener(newListener); }
  void addAsyncCoalescedSimulationListener(AsyncSimListener* newListener) { simNotifier.addAsyncCoalescedListener(newListener); }
  void removeAsyncSimulationListener(AsyncSimListener* listener) { simNotifier.removeListener(listener); }
  */
  
  
private:
  

  void initConcentrationCurve();
  
  void writeDescentToFile();

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
  
  // sample rate, calculated from current qcurve
  double sampleRate;
  
  // for filtering
  MultiButterworthLowPass filter;

  // for printing history to file
  Array<double> actionDescent;
  Array<Trajectory> trajDescent; // keep track of descent history in (q ; p) space
  
  
  
  
  

   
};

