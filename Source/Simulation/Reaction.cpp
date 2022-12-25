
#include "Reaction.h"
#include "EntityManager.h"

Reaction::Reaction(var params) : BaseItem(getTypeString() + " 1")
{

  reactant1 = addTargetParameter("Reactant 1", "Reactant 1", EntityManager::getInstance());
  reactant2 = addTargetParameter("Reactant 2", "Reactant 2", EntityManager::getInstance());
  product = addTargetParameter("Product", "Product", EntityManager::getInstance());

  reactant1->targetType = TargetParameter::CONTAINER;
  reactant1->maxDefaultSearchLevel = 0;

  reactant2->targetType = TargetParameter::CONTAINER;
  reactant2->maxDefaultSearchLevel = 0;

  product->targetType = TargetParameter::CONTAINER;
  product->maxDefaultSearchLevel = 0;

  assocRate = addFloatParameter("Association rate", "Reaction speed left to right", .5f, .0f, 1.f);
  dissocRate = addFloatParameter("Destruction rate", "Reaction speed right to left", .2f, .0f, 1.f);

  showWarningInUI = true;
}

Reaction::~Reaction()
{
}

void Reaction::onContainerParameterChangedInternal(Parameter *p)
{
  if (p == reactant1)
  {
    // unregister old one
    unregisterLinkedInspectable(linkedR1.get());
    if (linkedR1 != nullptr)
     ((Entity*)linkedR1.get())->enabled->removeParameterListener(this);
    // update new one
    linkedR1 = reactant1->targetContainer.get();
    registerLinkedInspectable(linkedR1.get());
    if (linkedR1 != nullptr)
      ((Entity*)linkedR1.get())->enabled->addParameterListener(this);
  }
  else if (p == reactant2)
  {
    unregisterLinkedInspectable(linkedR2.get());
    if (linkedR2 != nullptr)
      ((Entity*)linkedR2.get())->enabled->removeParameterListener(this);
    linkedR2 = reactant2->targetContainer.get();
    registerLinkedInspectable(linkedR2.get());
    if (linkedR2 != nullptr)
      ((Entity*)linkedR2.get())->enabled->addParameterListener(this);
  }
  else if (p == product)
  {
    unregisterLinkedInspectable(linkedP.get());
    if (linkedP != nullptr)
      ((Entity*)linkedP.get())->enabled->removeParameterListener(this);
    linkedP = product->targetContainer.get();
    registerLinkedInspectable(linkedP.get());
    if (linkedP != nullptr)
      ((Entity*)linkedP.get())->enabled->addParameterListener(this);
  }
  if (p == reactant1 || p == reactant2 || p == product)
    updateWarnings();
}

void Reaction::onExternalParameterValueChanged(Parameter *p)
{
  if ((linkedR1 != nullptr && p == ((Entity *)linkedR1.get())->enabled) || (linkedR2 != nullptr && p == ((Entity*)linkedR2.get())->enabled) || (linkedP != nullptr && p == ((Entity*)linkedP.get())->enabled))
    updateWarnings();
}

void Reaction::afterLoadJSONDataInternal()
{
  updateWarnings();
}

void Reaction::updateWarnings()
{
  if(isCurrentlyLoadingData) return;
  if (linkedR1 == nullptr || !((Entity *)linkedR1.get())->enabled->boolValue())
    setWarningMessage("Reactant 1 is null or disabled, this reaction will not be included in simulation","R1");
  else
    clearWarning("R1");

  if (linkedR2 == nullptr || !((Entity *)linkedR2.get())->enabled->boolValue())
    setWarningMessage("Reactant 2 is null or disabled, this reaction will not be included in simulation","R2");
  else
    clearWarning("R2");

  if (linkedP == nullptr || !((Entity *)linkedP.get())->enabled->boolValue())
    setWarningMessage("Product is null or disabled, this reaction will not be included in simulation","P");
  else
    clearWarning("P");
}

bool Reaction::shouldIncludeInSimulation()
{
  if (!enabled->boolValue())
    return false;
  if (linkedR1 == nullptr || !((Entity *)linkedR1.get())->enabled->boolValue())
    return false;
  if (linkedR2 == nullptr || !((Entity *)linkedR2.get())->enabled->boolValue())
    return false;
  if (linkedP == nullptr || !((Entity *)linkedP.get())->enabled->boolValue())
    return false;

  return true;
}
