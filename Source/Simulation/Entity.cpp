
#include "Entity.h"
#include "Simulation.h"

Entity::Entity(var params) : BaseItem(getTypeString() + " 1")
{
  primary = addBoolParameter("Primary", "Is the entity primary ?", true);
  creationRate = addFloatParameter("Creation rate", "Creation rate of the entity", .1f, .0f, 1.f);          // absolute
  destructionRate = addFloatParameter("Destruction rate", "Destruction rate of the entity", .1f, .0f, 1.f); // proportional to concentration
  concent = addFloatParameter("Concentration", "Concentration of the entity", .5f, .0f, 2.f);
  freeEnergy = addFloatParameter("Free energy", "Free energy of the entity", 0.f, -20.f, 10.f);
  draw = addBoolParameter("Draw", "Draw the entity", true);
  setHasCustomColor(true);
}

void Entity::fromSimEntity(SimEntity *e)
{
  primary->setValue(e->primary);
  creationRate->setValue(e->creationRate);
  destructionRate->setValue(e->destructionRate);
  concent->setValue(e->startConcent);
  freeEnergy->setValue(e->freeEnergy);
  e->entity = this;
  niceName = e->name;
  level=e->level;
  id=e->id;
  draw->setValue(e->draw);

  // todo composition
}

void Entity::onContainerParameterChangedInternal(Parameter *p)
{
  if (p == primary)
  {
    creationRate->hideInEditor = !primary->boolValue();
    // rebuild the whole inspector
    queuedNotifier.addMessage(new ContainerAsyncEvent(ContainerAsyncEvent::ControllableContainerNeedsRebuild, this));
    // other option: gray this field with creationRate->setEnabled(...);
  }
}

Entity::~Entity()
{
  composition.clear();
}
