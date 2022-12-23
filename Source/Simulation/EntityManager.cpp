

#include "EntityManager.h"

juce_ImplementSingleton(EntityManager);

EntityManager::EntityManager() : BaseManager("Entities")
{
	generateTrigger = addTrigger("Generate", "To generate entities");
}

EntityManager::~EntityManager()
{
}

void EntityManager::onContainerTriggerTriggered(Trigger *t)
{
	LOG("Trigger " << t->niceName);
}
