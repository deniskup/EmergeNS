
#include "Entity.h"

Entity::Entity(var params) :
    BaseItem(getTypeString() + " 1")
{
  primary = addBoolParameter("Primary", "Is the entity primary ?", true);
  concent= addFloatParameter("Concentration", "Concentration of the entity", .5f, .0f, 2.f);
  creationRate= addFloatParameter("Creation rate", "Creation rate of the entity", .1f, .0f, 1.f); //absolute
  destructionRate= addFloatParameter("Destruction rate", "Destruction rate of the entity", .1f, .0f, 1.f);; // proportional to concentration
  setHasCustomColor(true);
  
}

Entity::~Entity()
{
}

