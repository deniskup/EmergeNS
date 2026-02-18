

#pragma once

#include "Entity.h"

class EntityManager : public BaseManager<Entity>

{
public:
	juce_DeclareSingleton(EntityManager, true);
	EntityManager();
	~EntityManager();

	//Trigger *generateTrigger;

	void addItemInternal(Entity *e, var params) override;

	//void onContainerTriggerTriggered(Trigger *t) override;

	//void computeReachedEntReacs();
	// compute the number of each primary entities incomposite ones from the reactions, and check validity
	// return -1 if failed, number of primary entities otherwise
	//int computeCompositions();

	// normalise energies by setting primary entities to zero and propogating to composite ones
	//void normEnergies();

	Entity *getEntityFromName(String name);
  
  void setEntityToPatchID(int);

};
