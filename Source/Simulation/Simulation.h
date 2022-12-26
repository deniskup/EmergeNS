

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
  SimEntity(bool isPrimary, float concent, float cRate, float dRate);


  String name;
  Entity* entity; //sourceEntity
  
  Colour color;
  bool primary;
  float concent;
  float creationRate;
  float destructionRate;

  void increase(float incr);
  void decrease(float decr);

  String toString() const;
};

class SimReaction
{
public:
  SimReaction(Reaction *e);
  SimReaction(SimEntity* r1, SimEntity* r2, SimEntity* p, float assocRate, float dissocRate);
  
  SimEntity* reactant1;
  SimEntity* reactant2;
  SimEntity* product;

  

  float assocRate;
  float dissocRate;
};

class Simulation : public ControllableContainer,
                   public Thread

{
public:
  juce_DeclareSingleton(Simulation, true);
  Simulation();
  ~Simulation();

  IntParameter *maxSteps;
  IntParameter *curStep;
  BoolParameter *finished;
  FloatParameter *dt; //milliseconds
  FloatParameter *totalTime; //seconds

  Trigger *startTrigger;
  Trigger *cancelTrigger;

  OwnedArray<SimEntity> entities;    // all entities
  OwnedArray<SimReaction> reactions; // all reactions

  void start();
  void nextStep();
  void stop();
  void cancel();

  void run() override;

  SimEntity* getSimEntityForEntity(Entity* e);

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
};
