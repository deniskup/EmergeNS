

#include "ReactionManager.h"

#include "Simulation.h"

juce_ImplementSingleton(ReactionManager);

ReactionManager::ReactionManager() : BaseManager("Reactions")
{

}

ReactionManager::~ReactionManager()
{
}

void ReactionManager::importFromSim(Simulation *)
{
}
