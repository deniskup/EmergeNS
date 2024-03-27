

#pragma once
#include <JuceHeader.h>
#include "PAC.h"
#include "SteadyStates.h"
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

  bool constructionFailed=false;
  
  String name;
  Entity *entity = nullptr; // sourceEntity

  Colour color;
  bool primary;
  int id=-1; // unique identifier
  float concent;
  float startConcent;
  float previousConcent;
  float creationRate;
  float destructionRate;
  float freeEnergy;

  float change=0.f; // variation of concentration in the last dt

  bool reached; //is the entity reached from primary entities ?

  void importFromManual(); // retrieve info from pointer to Manual settings

  bool enabled = true;
  bool toImport=false; // the corresponding entity has been modified

  int level;
  bool draw = true;

  Compo composition; // indexes are link to primary entities thanks to array primEnts

  int idSAT = 0; // identifier for SAT Solving

  void increase(float incr);
  void decrease(float decr);
  void refresh();
  void nameFromCompo();

  String toString() const;

  JUCE_DECLARE_NON_COPYABLE_WITH_LEAK_DETECTOR(SimEntity);
};

typedef pair<SimEntity *, SimEntity *> Decomp;

class SimReaction
{
public:
  SimReaction(Reaction *);
  SimReaction(SimEntity *r1, SimEntity *r2, SimEntity *p, float assocRate, float dissocRate, float barrier = 0.f);
  SimReaction(Array<SimEntity *> r, Array<SimEntity *> p, float assocRate, float dissocRate, float barrier = 0.f);


  SimReaction(var data); // import from JSON
  var toJSONData();      // save to JSON

  bool constructionFailed=false;

  Reaction *reaction; // sourceReaction

  //old reactions 1+1<->1
  // SimEntity *reactant1;
  // SimEntity *reactant2;
  // SimEntity *product;

  Array<SimEntity *> reactants;
  Array<SimEntity *> products;

  bool isReversible=true; //can the reaction go the other way ?
  bool enabled = true; // to know if the reaction is enabled or not

  bool toImport=false; // the corresponding reaction has been modified

    bool reached; //is the reaction reached from primary entities ?

  String name; //by default a+b=c, but not forced

  void setName();

  float assocRate;
  float dissocRate;
  float energy = -1.0f; // energy of the reaction, -1 if not set

  void computeRate(bool noBarrier = false, bool noFreeEnergy = false);
  void computeBarrier();

  void importFromManual(); // retrieve info from pointer to Manual settings

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

  bool express=false; // express mode : no graphics, just find equilibrium

  // for drawing
  int maxSteps;
  int curStep;
  IntParameter *perCent;
  BoolParameter *finished;
  FloatParameter *dt;
  FloatParameter *totalTime;
  //BoolParameter *loadToManualByDefault;
  BoolParameter *autoScale;
  IntParameter *pointsDrawn;
  BoolParameter *detectEquilibrium;
  FloatParameter *epsilonEq;

  // to explore variants
  BoolParameter *ignoreFreeEnergy;
  BoolParameter *ignoreBarriers;

  EnumParameter *setCAC;
  EnumParameter *setSteadyState;

  void affectSATIds(); // affect idSAT to the entities/reactions if not already done.


  // actually just equal to not generated
  //  bool manualUpdate = false; //to put to true after loading to manual: adjust behaviours based on manual changes

  void establishLinks(); // establish links between lists and simulations, via names

  void importFromManual(); // import from manual changes using pointers
  void updateConcentLists(); //for each entity in the list, import its concentration from its simentity

  void computeRates();    // compute rates of reactions from their barriers and energy of entities
  void computeBarriers(); // compute barriers from rates and energy of entities

  void setConcToCAC(int idCAC); // set concentrations to CAC witness
  void setConcToSteadyState(int idSS); // set concentrations to Steady State

  bool toImport = false; // to know if we have to import from manual changes
  bool ready;            // to know if ready to be launched, ie parameters generated
  float recordConcent;   // record the higher concentration reached
  String recordEntity;
  float recordDrawn; // same but only for drawn entities for autoscale
  String recordDrawnEntity;
  float maxVarSpeed; // maximal variation speed in the last dt among entities

  int checkPoint; // every checkPoint steps, wait and log
  bool displayLog = false;
  Array<SimEntity *> entitiesDrawn;

  // these ones are for display
  FloatParameter *maxConcent;
  BoolParameter *realTime; // do we print intermediary steps ?
  // for alignment of simulation and RACs
  int leftMargin = 50;
  int rightMargin = 10;

  Trigger *genTrigger;
  Trigger *startTrigger;
  Trigger *genstartTrigger;
  Trigger *restartTrigger;
  Trigger *cancelTrigger;

  OwnedArray<SimEntity> entities;    // all entities
  OwnedArray<SimReaction> reactions; // all reactions
  Array<SimEntity *> primEnts;       // primary entities, useful to recover the number i

  int numLevels = -1;

  // gestion des PACs
  unique_ptr<PAClist> pacList;
  BoolParameter *oneColor; // to display RACs
  bool PACsGenerated = false;

  //is a PAC/CAC computation currently happening
  bool isComputing=false;
  bool shouldStop=false; //the stop button has been pressed
  bool shouldUpdate=false; //CAC list has to be refreshed

  // todo search and replace cycles to pacList->cycles etc in relevant files

  // different from the default getJSONData and loadJSONData which only saves parameters.
  var toJSONData();
  void importJSONData(var data);
  
struct tempReaction // TO REMOVE, only temporary
  {
    vector<pair<SimEntity*, int>> reactants;
    vector<pair<SimEntity*, int>> products;
  };

  void importCsvData(String); //tkosc.
  void SearchReversibleReactionsInCsvFile(); // to be called only in importCsvData

  

  void writeJSONConcents(string filename="");
  var concent2JSON(); // save start concentrations and current concentrations of entities
  

  //void filterReached(); // compute reached entities and reactions and keep only those

  // steady states
  unique_ptr<SteadyStateslist> steadyStatesList;


  void clearParams();
  void updateParams(); // for display
  void fetchGenerate();
  void fetchManual();
  void loadToManualMode();
  void start(bool restart = true);
  void nextStep();
  void stop();
  void cancel();

  // the thread function
  void run() override;


  SimEntity *getSimEntityForName(String);

  SimReaction *getSimReactionForName(String);

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
