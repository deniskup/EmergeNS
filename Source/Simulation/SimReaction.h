/*
  ==============================================================================

	SimReaction.h
	Created: 29 Sep 2024 11:09:45am
	Author:  bkupe

  ==============================================================================
*/

#pragma once

#include "JuceHeader.h"
#include "SimulationHelpers.h"
#include "ReactionManager.h"
#include <cmath>

class Reaction;
class SimEntity;
using namespace juce;

class SimReaction
{
public:
	SimReaction(Reaction*);
	SimReaction(SimEntity* r1, SimEntity* r2, SimEntity* p, float assocRate, float dissocRate, float barrier = 0.f);
	SimReaction(Array<SimEntity*> r, Array<SimEntity*> p, float assocRate, float dissocRate, float barrier = 0.f);

	void updateFromReaction(Reaction* r);


	SimReaction(var data); // import from JSON
	var toJSONData();      // save to JSON

	~SimReaction(); //delete and remove pointers to it

	bool constructionFailed = false;

	Reaction* reaction; // sourceReaction

	Array<SimEntity*> reactants;
	Array<SimEntity*> products;

	bool isReversible = true; //can the reaction go the other way ?
	bool enabled = true; // to know if the reaction is enabled or not
	bool generatedFromUserList = true; // the reaction has been generated from the user list
	bool toImport = false; // the corresponding reaction has been modified

	bool reached; //is the reaction reached from primary entities ?

	String name; //by default a+b=c, but not forced

	void autoSetName();

	float assocRate;
	float dissocRate;
  double micro_assocRate;
  double micro_dissocRate;
  float energy = -1.0f; // energy of the reaction, -1 if not set
  
  double volAvogadro = 1.; // volume * avogadro, quantity needed for stochastic simulations

	void computeRate(bool noBarrier = false, bool noFreeEnergy = false); // #tkosc TODO should rename this function it calculates the kinetic constant rates and not the reaction rates. I suggest computeConstantRates(***)
  void computeMicroRateConstants(); // kinetic rate constants associated to mass action law expressed with number of entities instead of concentrations

  void computeBarrier();

	//void importFromManual(); // retrieve info from pointer to Manual settings

	int idSAT = 0; // identifier for SAT Solving
	float flow;    // flow = dProduct/dt due to the reaction
	bool flowdir;  // direction of the flow, same convention as in PAC

	
	bool containsReactant(SimEntity* e);
	bool containsProduct(SimEntity* e);
	bool contains(SimEntity* e);

	int stoechiometryOfEntity(SimEntity* e);
  
  void setVolAvogadro(double va){volAvogadro = va;};
  
  //void setDirectWiener(float f){directWiener = f;};

  //void setReverseWiener(float f){reverseWiener = f;};

  
	JUCE_DECLARE_NON_COPYABLE_WITH_LEAK_DETECTOR(SimReaction);
};

