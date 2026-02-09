#pragma once
#include <JuceHeader.h>
#include "PAC.h"
#include "SteadyStates.h"
#include "SimReaction.h"
#include "SimEntity.h"
#include "SimulationHelpers.h"
#include "PhasePlane.h"
#include "Space.h"
#include "KineticLaw.h"
#include <random>


using namespace juce;
using namespace std;

class Entity;
class Reaction;
/*
class ConcentrationGrid // represents concentrations of entities over all the space grid
{
  public:
    Array<float> concent;
    int patchID;
}
*/
/*
struct PairHash {
    std::size_t operator()(const std::pair<int, SimEntity*>& p) const noexcept {
        return std::hash<int>()(p.first) ^ (std::hash<int>()(p.second->idSAT) << 1);
    }
};
// unordered_map[ pair< patch id , sim entity > , concentration ]
// represents concentrations of entities over all the space grid at a given time
typedef unordered_map<pair<int, SimEntity*>, float, PairHash> ConcentrationGrid;
 
 */






class Simulation : public ControllableContainer,
	public Thread

{
public:
	juce_DeclareSingleton(Simulation, true);
	Simulation();
	~Simulation();

	IntParameter* perCent;
	BoolParameter* finished;
	FloatParameter* dt;
	FloatParameter* totalTime;
	//BoolParameter *loadToManualByDefault;
	BoolParameter* autoScale;
	IntParameter* pointsDrawn;
	BoolParameter* detectEquilibrium;
	FloatParameter* epsilonEq;

	// to explore variants
	BoolParameter* ignoreFreeEnergy;
	BoolParameter* ignoreBarriers;
  
  // demographic noise
  BoolParameter* stochasticity;
  
  // simulation in space
  BoolParameter * isSpace;
  
  
	EnumParameter* setCAC;
  EnumParameter* setSteadyState;
	EnumParameter* setRun;

	Trigger* genTrigger;
	Trigger* startTrigger;
	Trigger* genstartTrigger;
	Trigger* restartTrigger;
	Trigger* cancelTrigger;

	// these ones are for display
	FloatParameter* maxConcent;
  BoolParameter* realTime; // do we print intermediary steps ?

	BoolParameter* liveUpdate;


	//REARRANGER POUR QUE CE SOIT LISIBLE ET LOGIQUE

  //OwnedArray<RACHist> RAChistory; // to store RAC activity at each step
  OwnedArray<OwnedArray<RACHist>> RAChistory; // to store RAC activity at each step for each run. x-axis : rundID. y axis : pacID
  //unique_ptr<DynamicsHistory> dynHistory; // to store simulation dynamics
	DynamicsHistory * dynHistory; // to store simulation dynamics
	bool express = false; // express mode : no graphics, just find equilibrium
  bool redrawRun = false; // redraw mode : just graphics, no simulation
  bool redrawPatch = false; // redraw mode : just graphics, no simulation
  
  // kinetics
  KineticLaw * kinetics;

	// step counters
	int maxSteps; // totaltime / dt
	int curStep; // step counter, start from 0, not re-init for new runs
	int nSteps; // step counter, start from 1, reset to 0 for each run
  
  // for drawing
  int runToDraw = 0;
  int patchToDraw = 0;
  
  // multiple runs
  int currentRun = 0;
  int nRuns = 1;
  bool isMultipleRun = false;
  Array<map<String, float>> initialConcentrations;
  bool shouldStartNewRun = false;

	//bool toImport = false; // to know if we have to import from manual changes
	//bool ready;            // to know if ready to be launched, ie parameters generated
  //float recordConcent;   // record the higher concentration reached #TODO --> should become an Array float of size nPatch
	Array<float> recordConcent;   // record the higher concentration reached #TODO --> should become an Array float of size nPatch
  //String recordEntity;
	Array<String> recordEntity;
  //float recordDrawn; // same but only for drawn entities for autoscale
	Array<float> recordDrawn; // same but only for drawn entities for autoscale
  //String recordDrawnEntity;
	Array<String> recordDrawnEntity;
  //float maxVarSpeed; // maximal variation speed in the last dt among entities
	Array<float> maxVarSpeed; // maximal variation speed in the last dt among entities

	int checkPoint; // every checkPoint steps, wait and log
	bool displayLog = false;
	Array<SimEntity*> entitiesDrawn;

	OwnedArray<SimEntity> entities;    // all entities
	OwnedArray<SimReaction> reactions; // all reactions
	Array<SimEntity*> primEnts;       // primary entities, useful to recover the number i

	int numLevels = -1;

	// gestion des PACs
	unique_ptr<PAClist> pacList;
	BoolParameter* oneColor; // to display RACs
	bool PACsGenerated = false;

	//is a PAC/CAC computation currently happening
	bool isComputing = false;
	bool shouldStop = false; //the stop button has been pressed
	bool shouldUpdate = false; //CAC list has to be refreshed

	// steady states
	unique_ptr<SteadyStateslist> steadyStatesList;
  
  
  // phase planes
  //unique_ptr<PhasePlane> phasePlane;


	enum SimulationState
	{
		Generating,
		Simulating,
		Idle
	};

	SimulationState state = Idle;
  std::atomic<bool> requestNewRun {false}; // to request thread (outside from it) to move to next run


	void affectSATIds(); // affect idSAT to the entities/reactions if not already done.


	// actually just equal to not generated
	//  bool manualUpdate = false; //to put to true after loading to manual: adjust behaviours based on manual changes
	// 
  // 
	  //REFACTOR, TO REMOVE ?
	//void importFromManual(); // import from manual changes using pointers
	//void establishLinks(); // establish links between lists and simulations, via names


	void computeIsolated(); // compute isolated entities

	void updateConcentLists(); //for each entity in the list, import its concentration from its simentity

	void computeRates();    // compute rates of reactions from their barriers and energy of entities
	void computeBarriers(); // compute barriers from rates and energy of entities

	void setConcToCAC(int idCAC); // set concentrations to CAC witness
	void setConcToSteadyState(OwnedArray<SimEntity>&, int idSS); // set concentrations to Steady State
  void drawConcOfRun(int idrun); // draw concentration dynamics associated to idrun
  void drawConcOfPatch(int idpatch); // draw concentration dynamics associated to idpatch

	// todo search and replace cycles to pacList->cycles etc in relevant files

	// different from the default getJSONData and loadJSONData which only saves parameters.
	var toJSONData();
	void importJSONData(var data);

	struct tempReaction // TO REMOVE, only temporary
	{
		vector<std::pair<SimEntity*, int>> reactants;
		vector<std::pair<SimEntity*, int>> products;
	};

	void importCsvData(String); 
	void SearchReversibleReactionsInCsvFile(); // to be called only in importCsvData

	bool getUserListMode(); // to know if we are in user list mode

	// print simulation content
	void PrintSimuToFile(string);

	void writeJSONConcents(string filename = "");
	var concent2JSON(); // save start concentrations and current concentrations of entities

	void writeHistory();


	//void filterReached(); // compute reached entities and reactions and keep only those


	void clearParams();
	void updateParams(); // for display
  void updateSpaceGridSizeInSimu();

	void fetchGenerate();
	
	void generateSimFromUserList();
  //void updateUserListFromSim();
	void updateUserListFromSim(int);
  void resetBeforeRunning();
	void start(bool restart = true);
  void startMultipleRuns(Array<map<String, float>> initConc);
  void requestToMoveToNextRun(){requestNewRun.store(true, std::memory_order_release);}
  int checkRunStatus();
  void resetForNextRun();
  void nextRedrawStep(ConcentrationSnapshot, Array<RACSnapshot>);
  void nextStep();
  void updateSinglePatchRates(Patch&, bool);
  //void SteppingReactionRates(OwnedArray<SimReaction>&, int, bool);
  //void SteppingInflowOutflowRates(OwnedArray<SimEntity>&, int);
	//void SteppingDiffusionRates(Patch&);
  void computeRACsActivity(bool);
	void stop();
	void cancel();


	// the thread function
	void run() override;


	SimEntity* getSimEntityForName(const String& name);
  SimEntity* getSimEntityForID(const size_t id);
  SimReaction* getSimReactionForName(const String& name);

	void onContainerTriggerTriggered(Trigger* t) override;
	void onContainerParameterChanged(Parameter* p) override;

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
      int _run = 0,
      //int _patch = 0,
			int nStep = 0,
      //Array<float> entityValues = Array<float>(),
      ConcentrationGrid entityValues = {},
			Array<Colour> entityColors = Array<Colour>(),
			Array<float> PACsValues = Array<float>(),
			Array<bool> RACList = Array<bool>())
			: type(t), sim(sim), run(_run), nStep(nStep), entityValues(entityValues), entityColors(entityColors), PACsValues(PACsValues), RACList(RACList)
		{
		}

    /*
    SimulationEvent(Type t,
      Simulation* sim,
      int _run = 0,
      int curStep = 0,
      Array<float> entityValues = Array<float>(),
      Array<Colour> entityColors = Array<Colour>(),
      Array<float> PACsValues = Array<float>(),
      map<PAC*, bool> RACList = map<PAC*, bool>())
      : type(t), sim(sim), curStep(curStep), entityValues(entityValues), entityColors(entityColors), PACsValues(PACsValues), RACList(RACList), run(_run)
    {
    }
    */
		Type type;
		Simulation* sim;
    int run;
    //int patch;
		int nStep;
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
};

