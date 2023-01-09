

#include "EntityManager.h"

juce_ImplementSingleton(EntityManager);

EntityManager::EntityManager() : BaseManager("Entities")
{
	generateTrigger = addTrigger("Generate", "To generate entities");
}

EntityManager::~EntityManager()
{
}

void EntityManager::addItemInternal(Entity *e, var params)
{
	if(isCurrentlyLoadingData) return;
	Colour c=Colour::fromHSV(.3f* items.size(),1,1,1);

	e->itemColor->setColor(c);
}

void EntityManager::onContainerTriggerTriggered(Trigger *t)
{
	LOG("Trigger " << t->niceName);
}
