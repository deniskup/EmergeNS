

#pragma once

#include <JuceHeader.h>
using namespace juce;
using namespace std;

// class Entity
// {
// public:
//   Entity(int x, bool b, float s, float c, float d);
//   ~Entity() {}

//   
// };


// class Reaction
// {
// public:
//   Array<Entity *> reactants;
//   Array<Entity *> products;
//   float assocRate; // from reactants to product
//   float dissocRate; //vice versa
//   Reaction(Array<Entity *> r, Array<Entity *> p, float ar, float dr)
//   {
//     reactants = r;
//     products = p;
//     assocRate = ar;
//     dissocRate = dr;
//   }
//   ~Reaction() {}
// };

class Simulation : 
  public ControllableContainer,
  public Thread
  
{
public:
  juce_DeclareSingleton(Simulation, true);
  Simulation();
  ~Simulation();

  // int maxSteps = 0;
  // int curStep = 0;
  // bool finished = false;
  // OwnedArray<Entity> entities;    // all entities
  // OwnedArray<Reaction> reactions; // all reactions
  // int nbReactions;

  // void setup(int m, Array<Entity *> e, Array<Reaction *> r);
  // void start();
  // void nextStep();
  // void stop();
  // void cancel();
  
  void run() override;

  class  SimulationListener
	{
	public:
		/** Destructor. */
		virtual ~SimulationListener() {}
		virtual void newStep(Simulation *) {};
		virtual void simulationFinished(Simulation *) {};
	};

	ListenerList<SimulationListener> listeners;
	void addSimulationListener(SimulationListener* newListener) { listeners.add(newListener); }
	void removeSimulationListener(SimulationListener* listener) { listeners.remove(listener); }
};
