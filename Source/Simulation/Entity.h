
#pragma once

#include "JuceHeader.h"

class Entity :
    public BaseItem
{
public:
    Entity(var params = var());
    ~Entity();

  // int id;
   BoolParameter* primary;
   FloatParameter* concent;
   FloatParameter* creationRate; // absolute
   FloatParameter* destructionRate; // proportional to concentration
   FloatParameter* freeEnergy; 


DECLARE_TYPE("Entity");
};

