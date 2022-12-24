
#pragma once

#include "JuceHeader.h"

class Reaction :
    public BaseItem
{
public:
    Reaction(var params = var());
    ~Reaction();

  // int id;
   TargetParameter* reactant1;
   TargetParameter* reactant2;
   TargetParameter* product;
   
   FloatParameter* assocRate; // reactants to product
   FloatParameter* dissocRate; // product to reactants

   WeakReference<ControllableContainer> linkedR1;
   WeakReference<ControllableContainer> linkedR2;
   WeakReference<ControllableContainer> linkedP;

   void onContainerParameterChangedInternal(Parameter* p) override;

DECLARE_TYPE("Reaction");
};

// class Reaction
// {
// public:
//   Array<Entity *> reactants;
//   Array<Entity *> products;
//   float assocRate; // from reactants to product
//   float dissocRate; //vice versa
//   Reaction(Array<Entity *> r, Array<Entity *> p, float ar, float dr)
//   {
//     reactants = r;
//     products = p;
//     assocRate = ar;
//     dissocRate = dr;
//   }
//   ~Reaction() {}
// };