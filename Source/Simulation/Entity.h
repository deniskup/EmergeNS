
#pragma once

#include "JuceHeader.h"

#include <unordered_map>

//using namespace juce;

class SimEntity;

class Entity : public BaseItem
{
public:
	Entity(juce::var params = juce::var());
  //Entity(SimEntity* e);
	Entity(SimEntity* e, int patchid);
	~Entity();

	BoolParameter* primary;
	BoolParameter* chemostat;
	FloatParameter* startConcent;
	FloatParameter* concent;
	FloatParameter* creationRate;    // absolute
	FloatParameter* destructionRate; // proportional to concentration
	FloatParameter* freeEnergy;
	BoolParameter* draw;
	
	//for Gillespie (probably unnecessary)
    // int startNumber; //start number of entities for Gillespie mode
	// int number; //current number of entities for Gillespie mode

	SimEntity* simEnt = nullptr; // corresponding simEntity

	int id = -1; //will be used as index for primary entities
	int level = -1;
	juce::Array<int> composition; // number of each primary entities
	bool compHasBeenSet = false;
	bool colorIsSet = false;

	bool reached = true; // can this entity be built from primary entities ?
  
  int patchid = 0; // patchID of entity represented

  bool updateSimEntityOnValueChanged = true;

	void updateInterface();
	void onContainerParameterChanged(Parameter *) override;

	DECLARE_TYPE("Entity");
};
