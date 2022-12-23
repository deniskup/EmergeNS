
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

   void increase(float incr);
   void decrease(float decr);

DECLARE_TYPE("Entity");
};

