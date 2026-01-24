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
#include "nlopt.hpp"
#include <random>
//#include "Simulation.h"

class Simulation;

using namespace std;

//class Simulation;
//class Simulation::SimulationEvent;
//class Simulation::AsyncSimListener;

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

/*
// class for filtering
class MultiButterworthLowPass
{
public:


  void setCutoffFrequency(double _cutoffHz)
  {
    cutoffHz = _cutoffHz;
  }
  
  void setSamplingRate(double _sampRate)
  {
    sampRate = _sampRate;
  }
  
  
  void process(Array<Array<double>> & data)
  {
    if (data.size()==0)
      return;
    
    const int nChannels = data.getUnchecked(0).size();
    const int nSamples = data.size();
    constexpr auto PI = 3.141592653589793f;
    dnBuffer.resize(nChannels, 0.f);
    
    const double tan = std::tan(PI * cutoffHz / sampRate);
    const double a1 = (tan - 1.f) / (tan + 1.f);
    
    for (int channel=0; channel<nChannels; channel++)
    {
      // retrieve signal for this particular channel
      vector<double> channelSample;
      for (int point=0; point<nSamples; point++)
      {
        channelSample.push_back(data.getUnchecked(point).getUnchecked(channel));
      }
      
      for (int i=0; i<nSamples; i++)
      {
        double inputSample = channelSample[i];
        double allpassFilteredSample = a1 * inputSample + dnBuffer[channel];
        dnBuffer[channel] = inputSample - a1*allpassFilteredSample;
        double filterOutput = 0.5f * (inputSample + allpassFilteredSample);
        channelSample[i] = filterOutput;
      }
      
      // write it to data
      for (int i=0; i<nSamples; i++)
      {
        data.getUnchecked(i).setUnchecked(channel, channelSample[i]);
      }
      
    }
  } // end process method

private:
    double cutoffHz = 1.;
    double sampRate = 1.;
    vector<double> dnBuffer;
    juce::OwnedArray<juce::dsp::IIR::Filter<float>> filters;
};
*/


class LiftTrajectoryOptResults
{
  public:
    LiftTrajectoryOptResults(){};
    ~LiftTrajectoryOptResults(){};
    Array<StateVec> opt_momentum;
    Array<double> opt_deltaT;
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
  FloatParameter * timescale_factor;

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
  

  void initConcentrationCurve();
  
  void writeDescentToFile();
  
  void filterConcentrationTrajectory();
  
  void updateDescentParams();
  
  bool descentShouldUpdateParams(double);
  
  bool descentShouldContinue(int);
  
  LiftTrajectoryOptResults liftCurveToTrajectoryWithKinSolve();

  LiftTrajectoryOptResults liftCurveToTrajectoryWithNLOPT();
  
  void updateOptimalConcentrationCurve_old(const Array<StateVec> popt, const Array<double> deltaTopt);
  void updateOptimalConcentrationCurve();

  double calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t);
  
  double backTrackingMethodForStepSize(const Curve& c, const Curve& deltac);
  
  //filtering
  void applyButterworthFilter(juce::Array<double>&, std::vector<juce::dsp::IIR::Filter<double>>&);
  //vector<juce::dsp::IIR::Filter<double>> makeFilters(ReferenceCountedArray<IIRCoefficients>);
  void lowPassFiltering(Array<StateVec>&);
  
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
  Array<StateVec> dAdq, dAdq_filt;

  
  // sample rate, calculated from current qcurve
  double sampleRate;
  
  // #para
  double stepDescentThreshold = 1e-4;
  double stepDescent = 1.;
  
  // for filtering
  //MultiButterworthLowPass filter;

  // for printing history to file
  Array<double> actionDescent;
  Array<Trajectory> trajDescent; // keep track of descent history in (q ; p) space
  Array<Trajectory> dAdqDescent; // keep track of gradient history
  Array<Trajectory> dAdqDescent_filt; // keep track of filtered gradient history
  
  
  
  void debugNEPImplementation();

  void debugFiltering();
  
  bool bDebug = false;
  ofstream debugfile;

  

   
};

