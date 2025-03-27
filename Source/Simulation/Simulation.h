#pragma once
#include <JuceHeader.h>
#include "PAC.h"
#include "SteadyStates.h"
#include "SimEntity.h"
#include "SimReaction.h"
#include "SimulationHelpers.h"
#include "PhasePlane.h"
#include <random>


using namespace juce;
using namespace std;

class Entity;
class Reaction;


class RandomGausGenerator
{
  public:
  RandomGausGenerator(float _mu, float _sigma) // constructor
  {
    mu = _mu;
    sigma = _sigma;
    gausDist = new normal_distribution<float>;
    normal_distribution<float> dtemp(mu, sigma);
    gausDist->param(dtemp.param());
    generator=new default_random_engine;
  };
  
  // attributes
  default_random_engine * generator;
  normal_distribution<float> * gausDist;
  float mu = 0.;
  float sigma = 1.;
  //unsined long seed;
  
  // generate actual random number
  float randomNumber()
  {
    return (*gausDist)(*generator);
  }
  
  void setFixedSeed(unsigned int _seed)
  {
    generator->seed(_seed);
  }
  
};




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
  RandomGausGenerator * rgg;
  float noiseEpsilon; // = 1. / sqrt(volume)
  
  
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
	bool express = false; // express mode : no graphics, just find equilibrium
  bool redraw = false; // redraw mode : just graphics, no simulation

	// for drawing
	int maxSteps;
	int curStep;
	int nSteps;
  
  // multiple runs
  int currentRun = 0;
  int nRuns = 1;
  bool isMultipleRun = false;
  Array<map<String, float>> initialConcentrations;
  bool shouldStartNewRun = false;

	//bool toImport = false; // to know if we have to import from manual changes
	//bool ready;            // to know if ready to be launched, ie parameters generated
	float recordConcent;   // record the higher concentration reached
	String recordEntity;
	float recordDrawn; // same but only for drawn entities for autoscale
	String recordDrawnEntity;
	float maxVarSpeed; // maximal variation speed in the last dt among entities

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
	void setConcToSteadyState(int idSS); // set concentrations to Steady State
  void drawConcOfRun(int idrun); // draw concentration dynamics associated to idrun

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
	void fetchGenerate();
	
	void generateSimFromUserList();
	void updateUserListFromSim();
  void resetBeforeRunning();
	void start(bool restart = true);
  void startMultipleRuns(Array<map<String, float>> initConc);
	void nextStep();
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
      DRAWRUN
		};

		SimulationEvent(Type t,
			Simulation* sim,
      int _run = 0,
			int curStep = 0,
			Array<float> entityValues = Array<float>(),
			Array<Colour> entityColors = Array<Colour>(),
			Array<float> PACsValues = Array<float>(),
			Array<bool> RACList = Array<bool>())
			: type(t), sim(sim), curStep(curStep), entityValues(entityValues), entityColors(entityColors), PACsValues(PACsValues), RACList(RACList), run(_run)
		{
		}

		Type type;
		Simulation* sim;
    int run;
		int curStep;
		Array<float> entityValues;
		Array<Colour> entityColors;
		Array<float> PACsValues;
		Array<bool> RACList;
	};

	QueuedNotifier<SimulationEvent> simNotifier;
	typedef QueuedNotifier<SimulationEvent>::Listener AsyncSimListener;

	void addAsyncSimulationListener(AsyncSimListener* newListener) { simNotifier.addListener(newListener); }
	void addAsyncCoalescedSimulationListener(AsyncSimListener* newListener) { simNotifier.addAsyncCoalescedListener(newListener); }
	void removeAsyncSimulationListener(AsyncSimListener* listener) { simNotifier.removeListener(listener); }
};

