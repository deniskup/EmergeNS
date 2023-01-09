
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

   void onContainerParameterChangedInternal(Parameter *p) override;


DECLARE_TYPE("Entity");
};

