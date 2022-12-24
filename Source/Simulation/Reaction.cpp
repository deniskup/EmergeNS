
#include "Reaction.h"
#include "EntityManager.h"

Reaction::Reaction(var params) :
    BaseItem(getTypeString() + " 1")
{
  
  reactant1= addTargetParameter("Reactant 1", "Reactant 1",EntityManager::getInstance());
  reactant2= addTargetParameter("Reactant 2", "Reactant 2",EntityManager::getInstance());
  product= addTargetParameter("Product 1", "Product 1",EntityManager::getInstance());

  reactant1->targetType = TargetParameter::CONTAINER;
  reactant1->maxDefaultSearchLevel = 0;

  reactant2->targetType = TargetParameter::CONTAINER;
  reactant2->maxDefaultSearchLevel = 0;

  product->targetType = TargetParameter::CONTAINER;
  product->maxDefaultSearchLevel = 0;



  assocRate= addFloatParameter("Association rate", "Reaction speed left to right", .5f, .0f, 1.f); 
  dissocRate= addFloatParameter("Destruction rate", "Reaction speed right to left", .2f, .0f, 1.f);
}

Reaction::~Reaction()
{
}

void Reaction::onContainerParameterChangedInternal(Parameter *p)
{
  if(p==reactant1)
  {
    //unregister old one
    unregisterLinkedInspectable(linkedR1.get());
    //update new one
    linkedR1 = reactant1->targetContainer.get();
    registerLinkedInspectable(linkedR1.get());
  } 
  else   if(p==reactant2)
  {
    unregisterLinkedInspectable(linkedR2.get());
    linkedR2 = reactant2->targetContainer.get();
    registerLinkedInspectable(linkedR2.get());
  } else   if(p==product)
  {
    unregisterLinkedInspectable(linkedP.get());
    linkedP = product->targetContainer.get();
    registerLinkedInspectable(linkedP.get());
  } 
}
