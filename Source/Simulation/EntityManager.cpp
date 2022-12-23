

#include "EntityManager.h"

juce_ImplementSingleton(EntityManager);

EntityManager::EntityManager() :
	BaseManager("Entities")
{
}

EntityManager::~EntityManager()
{
}

