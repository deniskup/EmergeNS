

#include "ReactionManager.h"

#include "Simulation.h"

juce_ImplementSingleton(ReactionManager);

ReactionManager::ReactionManager() : BaseManager("Reactions")
{

}

ReactionManager::~ReactionManager()
{
}

void ReactionManager::autoRename()
{
    for (auto &r : items){
        r->autoRename();
    }
}

void ReactionManager::inferAllReacs()
{
    for( auto &r: items){
        r->inferEntities();
    }
}
