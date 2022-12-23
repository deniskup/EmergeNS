
#include "Entity.h"

Entity::Entity(var params) :
    BaseItem(getTypeString() + " 1")
{
  primary = addBoolParameter("Primary", "Is the entity primary ?", true);
  concent= addFloatParameter("Concentration", "Concentration of the entity", .5f, .0f, 2.f);
  creationRate= addFloatParameter("Creation rate", "Creation rate of the entity", .1f, .0f, 1.f); //absolute
  destructionRate= addFloatParameter("Destruction rate", "Destruction rate of the entity", .1f, .0f, 1.f);; // proportional to concentration
}

Entity::~Entity()
{
}

void Entity::increase(float incr)
{
  concent->setValue(concent->floatValue() + incr);
}

void Entity::decrease(float decr)
{
  concent->setValue(jmax(0.f, concent->floatValue() - decr));
}