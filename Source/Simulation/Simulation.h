

#pragma once

#include <JuceHeader.h>
using namespace juce;
using namespace std;

class Entity;
class Reaction;

class SimEntity
{
public:
  SimEntity(Entity *e);
  SimEntity(bool isPrimary, float concent, float cRate, float dRate, float freeEnergy);

  String name;
  Entity *entity; // sourceEntity

  Colour color;
  bool primary;
  float concent;
  float creationRate;
  float destructionRate;
  float freeEnergy;

  int level;
  bool draw=true;


  void increase(float incr);
  void decrease(float decr);

  String toString() const;

  JUCE_DECLARE_NON_COPYABLE_WITH_LEAK_DETECTOR(SimEntity);
};

class SimReaction
{
public:
  SimReaction(Reaction *e);
  SimReaction(SimEntity *r1, SimEntity *r2, SimEntity *p, float assocRate, float dissocRate);

  SimEntity *reactant1;
  SimEntity *reactant2;
  SimEntity *product;

  float assocRate;
  float dissocRate;

  JUCE_DECLARE_NON_COPYABLE_WITH_LEAK_DETECTOR(SimReaction);
};

class Simulation : public ControllableContainer,
                   public Thread

{
public:
  juce_DeclareSingleton(Simulation, true);
  Simulation();
  ~Simulation();

  int maxSteps;
  int curStep;
  IntParameter *perCent;
  BoolParameter *finished;
  FloatParameter *dt;
  FloatParameter *totalTime;
  BoolParameter *generated;
  BoolParameter *autoScale;

  float recordConcent; // record the higher concentration reached
  String recordEntity;
  float recordDrawn; //same but only for drawn entities for autoscale
  String recordDrawnEntity;

  int checkPoint; // every checkPoint steps, wait and log
  bool displayLog=false;
  Array<SimEntity *> entitiesDrawn;

  // these ones are for display
  FloatParameter *maxConcent;
  BoolParameter *realTime; // do we print intermediary steps ?

  Trigger *startTrigger;
  Trigger *cancelTrigger;

  OwnedArray<SimEntity> entities;    // all entities
  OwnedArray<SimReaction> reactions; // all reactions

  void fetchGenerate();
  void fetchManual();
  void start();
  void nextStep();
  void stop();
  void cancel();

  void run() override;

  SimEntity *getSimEntityForEntity(Entity *e);

  void onContainerTriggerTriggered(Trigger *t) override;
  void onContainerParameterChanged(Parameter *p) override;

  class SimulationListener
  {
  public:
    virtual ~SimulationListener() {}
    virtual void newStep(Simulation *){};
    virtual void simulationWillStart(Simulation *){};
    virtual void simulationStarted(Simulation *){};
    virtual void simulationFinished(Simulation *){};
  };

  ListenerList<SimulationListener> listeners;
  void addSimulationListener(SimulationListener *newListener) { listeners.add(newListener); }
  void removeSimulationListener(SimulationListener *listener) { listeners.remove(listener); }

  	// ASYNC
	class  SimulationEvent
	{
	public:
		enum Type { WILL_START, STARTED, NEWSTEP, FINISHED };

		SimulationEvent(Type t, Simulation* sim, int curStep=0, Array<float> entityValues=Array<float>(), Array<Colour> entityColors=Array<Colour>()) :
			type(t), sim(sim), curStep(curStep), entityValues(entityValues), entityColors(entityColors)
		{
		}

		Type type;
		Simulation* sim;
		int curStep;
    Array<float> entityValues;
    Array<Colour> entityColors;
	};

	QueuedNotifier<SimulationEvent> simNotifier;
	typedef QueuedNotifier<SimulationEvent>::Listener AsyncSimListener;


	void addAsyncSimulationListener(AsyncSimListener* newListener) { simNotifier.addListener(newListener); }
	void addAsyncCoalescedSimulationListener(AsyncSimListener* newListener) { simNotifier.addAsyncCoalescedListener(newListener); }
	void removeAsyncSimulationListener(AsyncSimListener* listener) { simNotifier.removeListener(listener); }
};
