
#include "Entity.h"

Entity::Entity(var params) : BaseItem(getTypeString() + " 1")
{
  primary = addBoolParameter("Primary", "Is the entity primary ?", true);
  creationRate = addFloatParameter("Creation rate", "Creation rate of the entity", .1f, .0f, 1.f); // absolute
  destructionRate = addFloatParameter("Destruction rate", "Destruction rate of the entity", .1f, .0f, 1.f);
  ; // proportional to concentration
  concent = addFloatParameter("Concentration", "Concentration of the entity", .5f, .0f, 2.f);
  freeEnergy = addFloatParameter("Free energy", "Free energy of the entity", 0.f, -10.f, 10.f);
  ; // proportional to concentration
  setHasCustomColor(true);
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
}
