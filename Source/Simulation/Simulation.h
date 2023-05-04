

#pragma once
#include <JuceHeader.h>
#include "PAC.h"
using namespace juce;
using namespace std;

class Entity;
class Reaction;

typedef Array<int> Compo;

class SimEntity
{
public:
  SimEntity(Entity *e);
  SimEntity(bool isPrimary, float concent, float cRate, float dRate, float freeEnergy);

  SimEntity(var data); // import from JSON
  var toJSONData();    // save to JSON

  String name;
  Entity *entity; // sourceEntity

  Colour color;
  bool primary;
  int id; // unique identifier
  float concent;
  float startConcent;
  float creationRate;
  float destructionRate;
  float freeEnergy;

  void importFromManual(); //retrieve info from pointer to Manual settings

  bool enabled=true;

  int level;
  bool draw = true;

  Compo composition; // indexes are link to primary entities thanks to array primEnts

  int idSAT = 0; // identifier for SAT Solving

  void increase(float incr);
  void decrease(float decr);
  void nameFromCompo();

  String toString() const;

  JUCE_DECLARE_NON_COPYABLE_WITH_LEAK_DETECTOR(SimEntity);
};

typedef pair<SimEntity *, SimEntity *> Decomp;

class SimReaction
{
public:
  SimReaction(Reaction *);
  SimReaction(SimEntity *r1, SimEntity *r2, SimEntity *p, float assocRate, float dissocRate, float barrier=0.f);

  SimReaction(var data); // import from JSON
  var toJSONData();      // save to JSON

  Reaction *reaction; // sourceReaction

  SimEntity *reactant1;
  SimEntity *reactant2;
  SimEntity *product;

  bool enabled=true; // to know if the reaction is enabled or not

  String name; // should be a+b=c


  void setName();

  float assocRate;
  float dissocRate;
  float energy = -1.0f; // energy of the reaction, -1 if not set

  void computeRate(bool noBarrier = false, bool noFreeEnergy = false);
  void computeBarrier();

  void importFromManual(); //retrieve info from pointer to Manual settings

  int idSAT = 0; // identifier for SAT Solving
  float flow;    // flow = dProduct/dt due to the reaction
  bool flowdir;  // direction of the flow, same convention as in PAC

  bool contains(SimEntity *e);

  JUCE_DECLARE_NON_COPYABLE_WITH_LEAK_DETECTOR(SimReaction);
};

class Simulation : public ControllableContainer,
                   public Thread

{
public:
  juce_DeclareSingleton(Simulation, true);
  Simulation();
  ~Simulation();

  // for drawing
  int maxSteps;
  int curStep;
  IntParameter *perCent;
  BoolParameter *finished;
  FloatParameter *dt;
  FloatParameter *totalTime;
  BoolParameter *generated;
  BoolParameter *autoScale;
  IntParameter *pointsDrawn;

  // to explore variants
  BoolParameter *ignoreFreeEnergy;
  BoolParameter *ignoreBarriers;

 //actually just equal to not generated
 // bool manualUpdate = false; //to put to true after loading to manual: adjust behaviours based on manual changes

  void importFromManual();   // import from manual changes using pointers

  void computeRates();    // compute rates of reactions from their barriers and energy of entities
  void computeBarriers(); // compute barriers from rates and energy of entities

  bool ready;          // to know if ready to be launched, ie parameters generated
  float recordConcent; // record the higher concentration reached
  String recordEntity;
  float recordDrawn; // same but only for drawn entities for autoscale
  String recordDrawnEntity;

  int checkPoint; // every checkPoint steps, wait and log
  bool displayLog = false;
  Array<SimEntity *> entitiesDrawn;

  // these ones are for display
  FloatParameter *maxConcent;
  BoolParameter *realTime; // do we print intermediary steps ?

  Trigger *genTrigger;
  Trigger *startTrigger;
  Trigger *genstartTrigger;
  Trigger *restartTrigger;
  Trigger *cancelTrigger;

  OwnedArray<SimEntity> entities;    // all entities
  OwnedArray<SimReaction> reactions; // all reactions
  Array<SimEntity *> primEnts;       // primary entities, useful to recover the number i

  int numLevels=-1;

  // gestion des PACs
  unique_ptr<PAClist> pacList;
  BoolParameter *oneColor; // to display RACs
  bool PACsGenerated = false;

  // todo search and replace cycles to pacList->cycles etc in relevant files

  // different from the default getJSONData and loadJSONData which only saves parameters.
  var toJSONData();
  void importJSONData(var data);

  void clearParams();
  void updateParams(); // for display
  void fetchGenerate();
  void fetchManual();
  void loadToManualMode();
  void generate();
  void start();
  void nextStep();
  void stop();
  void cancel();

  // the thread function
  void run() override;

  SimEntity *getSimEntityForEntity(Entity *e);
  SimEntity *getSimEntityForID(int id);

  SimReaction *getSimReactionForID(int idSAT);

  void onContainerTriggerTriggered(Trigger *t) override;
  void onContainerParameterChanged(Parameter *p) override;

  // class SimulationListener
  // {
  // public:
  //   virtual ~SimulationListener() {}
  //   virtual void newStep(Simulation *){};
  //   virtual void simulationWillStart(Simulation *){};
  //   virtual void simulationStarted(Simulation *){};
  //   virtual void simulationFinished(Simulation *){};
  // };

  // ListenerList<SimulationListener> listeners;
  // void addSimulationListener(SimulationListener *newListener) { listeners.add(newListener); }
  // void removeSimulationListener(SimulationListener *listener) { listeners.remove(listener); }

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
      FINISHED
    };

    SimulationEvent(Type t,
                    Simulation *sim,
                    int curStep = 0,
                    Array<float> entityValues = Array<float>(),
                    Array<Colour> entityColors = Array<Colour>(),
                    Array<float> PACsValues = Array<float>(),
                    Array<bool> RACList = Array<bool>())
        : type(t), sim(sim), curStep(curStep), entityValues(entityValues), entityColors(entityColors), PACsValues(PACsValues), RACList(RACList)
    {
    }

    Type type;
    Simulation *sim;
    int curStep;
    Array<float> entityValues;
    Array<Colour> entityColors;
    Array<float> PACsValues;
    Array<bool> RACList;
  };

  QueuedNotifier<SimulationEvent> simNotifier;
  typedef QueuedNotifier<SimulationEvent>::Listener AsyncSimListener;

  void addAsyncSimulationListener(AsyncSimListener *newListener) { simNotifier.addListener(newListener); }
  void addAsyncCoalescedSimulationListener(AsyncSimListener *newListener) { simNotifier.addAsyncCoalescedListener(newListener); }
  void removeAsyncSimulationListener(AsyncSimListener *listener) { simNotifier.removeListener(listener); }
};

class CompoDecomps
{
public:
  CompoDecomps(Compo comp, Array<Decomp> ar) : compo(comp), decomps(ar) {}
  ~CompoDecomps()
  {
    decomps.clear();
  }
  Compo compo;
  Array<Decomp> decomps;
  void add(SimEntity *e1, SimEntity *e2)
  {
    decomps.add(make_pair(e1, e2));
  }
};