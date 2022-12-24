

#pragma once

#include <JuceHeader.h>
using namespace juce;
using namespace std;



class Entity;
class Reaction;

class Simulation : 
  public ControllableContainer,
  public Thread
  
{
public:
  juce_DeclareSingleton(Simulation, true);
  Simulation();
  ~Simulation();

   IntParameter* maxSteps;
   IntParameter* curStep;
   BoolParameter* finished;
   OwnedArray<Entity> entities;    // all entities
   OwnedArray<Reaction> reactions; // all reactions

   void setup(int m, Array<Entity *> e, Array<Reaction *> r);
   void start();
   void nextStep();
   void stop();
   void cancel();
  
  void run() override;

 class  SimulationListener
	{
	public:
		virtual ~SimulationListener() {}
		virtual void newStep(Simulation *) {};
		virtual void simulationFinished(Simulation *) {};
	};

	ListenerList<SimulationListener> listeners;
	void addSimulationListener(SimulationListener* newListener) { listeners.add(newListener); }
	void removeSimulationListener(SimulationListener* listener) { listeners.remove(listener); }
};
