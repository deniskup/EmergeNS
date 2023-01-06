
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

  energy = addFloatParameter("Energy Barrier", "Additional energy barrier of the reaction", 1.f, 0.f, 5.f);

  assocRate = addFloatParameter("Association rate", "Reaction speed left to right", .5f);
  dissocRate = addFloatParameter("Dissociation rate", "Reaction speed right to left", .5f);
  assocRate->setControllableFeedbackOnly(true);
  dissocRate->setControllableFeedbackOnly(true);

  showWarningInUI = true;
}

Reaction::~Reaction()
{
}

void Reaction::onContainerParameterChangedInternal(Parameter *p)
{
  // listen to parameter changes for the linked entities
  if (p == reactant1)
  {
    // unregister old one
    unregisterLinkedInspectable(linkedR1.get());
    if (linkedR1 != nullptr)
    {
      ((Entity *)linkedR1.get())->enabled->removeParameterListener(this);
      ((Entity *)linkedR1.get())->freeEnergy->removeParameterListener(this);
    }
    // update new one
    linkedR1 = reactant1->targetContainer.get();
    registerLinkedInspectable(linkedR1.get());
    if (linkedR1 != nullptr)
    {
      ((Entity *)linkedR1.get())->enabled->addParameterListener(this);
      ((Entity *)linkedR1.get())->freeEnergy->addParameterListener(this);
    }
  }
  else if (p == reactant2)
  {
    unregisterLinkedInspectable(linkedR2.get());
    if (linkedR2 != nullptr)
    {
      ((Entity *)linkedR2.get())->enabled->removeParameterListener(this);
      ((Entity *)linkedR2.get())->freeEnergy->removeParameterListener(this);
    }
    linkedR2 = reactant2->targetContainer.get();
    registerLinkedInspectable(linkedR2.get());
    if (linkedR2 != nullptr)
    {
      ((Entity *)linkedR2.get())->enabled->addParameterListener(this);
      ((Entity *)linkedR2.get())->freeEnergy->addParameterListener(this);
    }
  }
  else if (p == product)
  {
    unregisterLinkedInspectable(linkedP.get());
    if (linkedP != nullptr)
    {
      ((Entity *)linkedP.get())->enabled->removeParameterListener(this);
      ((Entity *)linkedP.get())->freeEnergy->removeParameterListener(this);
    }
    linkedP = product->targetContainer.get();
    registerLinkedInspectable(linkedP.get());
    if (linkedP != nullptr)
    {
      ((Entity *)linkedP.get())->enabled->addParameterListener(this);
      ((Entity *)linkedP.get())->freeEnergy->addParameterListener(this);
    }
  }
  updateWarnAndRates();
}

void Reaction::onExternalParameterValueChanged(Parameter *p)
{
  if (linkedR1 != nullptr)
  {
    Entity *r1 = (Entity *)linkedR1.get();
    if (p == r1->enabled || p == r1->freeEnergy)
      ;
    updateWarnAndRates();
  }
  if (linkedR2 != nullptr)
  {
    Entity *r2 = (Entity *)linkedR2.get();
    if (p == r2->enabled || p == r2->freeEnergy)
      ;
    updateWarnAndRates();
  }
  if (linkedP != nullptr)
  {
    Entity *pr = (Entity *)linkedP.get();
    if (p == pr->enabled || p == pr->freeEnergy)
      ;
    updateWarnAndRates();
  }
}

void Reaction::afterLoadJSONDataInternal()
{
  updateWarnAndRates();
}

void Reaction::updateWarnAndRates()
{
  if (isCurrentlyLoadingData)
    return;
  bool someWarn = false;

  if (linkedR1 == nullptr || !((Entity *)linkedR1.get())->enabled->boolValue())
  {
    setWarningMessage("Reactant 1 is null or disabled, this reaction will not be included in simulation", "R1");
    someWarn = true;
  }
  else
    clearWarning("R1");

  if (linkedR2 == nullptr || !((Entity *)linkedR2.get())->enabled->boolValue())
  {
    setWarningMessage("Reactant 2 is null or disabled, this reaction will not be included in simulation", "R2");
    someWarn = true;
  }
  else
    clearWarning("R2");

  if (linkedP == nullptr || !((Entity *)linkedP.get())->enabled->boolValue())
  {
    setWarningMessage("Product is null or disabled, this reaction will not be included in simulation", "P");
    someWarn = true;
  }
  else
    clearWarning("P");
  if (someWarn)
    return;
  // energies of reactants and products
  // GA+GB
  float energyLeft = ((Entity *)linkedR1.get())->freeEnergy->floatValue() + ((Entity *)linkedR2.get())->freeEnergy->floatValue();
  // GAB
  float energyRight = ((Entity *)linkedP.get())->freeEnergy->floatValue();
  // total energy G* of the reaction: activation + max of GA+GB and GAB.
  float energyStar = energy->floatValue() + jmax(energyLeft, energyRight);
  // k1=exp(GA+GB-G*)
  assocRate->setValue(exp(energyLeft - energyStar));
  // k2=exp(GAB-G*)
  float newDissocRate = exp(energyRight - energyStar);
  dissocRate->setValue(newDissocRate);
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
