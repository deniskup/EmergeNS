

#pragma once

#include "Entity.h"

class EntityManager :
	public BaseManager<Entity>
{
public:
	juce_DeclareSingleton(EntityManager,true);
	EntityManager();
	~EntityManager();

	Trigger* generateTrigger;

	void onContainerTriggerTriggered(Trigger* t) override;
};