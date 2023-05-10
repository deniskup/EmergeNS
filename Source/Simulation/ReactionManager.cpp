

#include "ReactionManager.h"

#include "Simulation.h"

juce_ImplementSingleton(ReactionManager);

ReactionManager::ReactionManager() : BaseManager("Reactions")
{

}

ReactionManager::~ReactionManager()
{
}

int ReactionManager::computeCompositions(){
    //TODO copy from globalactions
    return 0;
}
