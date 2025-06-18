// 
//  NEP.h
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//  kosc.thomas@gmail.com
//  nlopt library (used for optimizations) need to be installed
// Must modify the .jucer file to add :
// path to header files of nlopt
// -lnlopt to link to libraries
// TODO : modify

/*
- update read me for compilation with nlopt
- filtering of pcurve
- step size picking
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
  NEP(Simulation *simul) : ControllableContainer("NEP"), Thread("NEP"), simul(simul){};

  NEP(var data); // import from JSON
  ~NEP();
  
  Simulation * simul;
  
  Trigger * startDescent;
  
  EnumParameter* sst_stable;
  EnumParameter* sst_saddle;

  // update steady state list when updateParams is calle din SImulation
  void updateSteadyStateList();
  
  
  // methods called when container is modified
  void onContainerParameterChanged(Parameter* p) override;
  void onContainerTriggerTriggered(Trigger* t) override;
  void onChildContainerRemoved(ControllableContainer*) override;
  
  
  // thread function
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
  
  
  
private:
  

  void initConcentrationCurve();
  
  void writeDescentToFile();

  LiftTrajectoryOptResults liftCurveToTrajectory();
  
  void updateOptimalConcentrationCurve(const Array<StateVec> popt, const Array<double> deltaTopt);

  double calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t);
  
  double backTrackingMethodForStepSize(const Curve& c, const Curve& deltac);

  void extractHamiltonian(); // not needed ?
  
  pair<Trajectory, Trajectory>  integrateHamiltonEquations(StateVec, StateVec);
  
  // global variable describing the state of the descent
  Curve qcurve;
  pCurve pcurve;
  Array<double> times;
  double action;
  
  // some descent controling parameters
  int nPoints = 50; // #para
  double action_threshold = 0.01; // #para
  int maxIter = 15; // #para

  
  // for printing history to file
  Array<double> actionDescent;
  Array<Trajectory> trajDescent; // keep track of descent history in (q ; p) space
  
  

   
};

