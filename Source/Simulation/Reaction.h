
#pragma once

#include "JuceHeader.h"

class SimReaction;

class Reaction : public BaseItem
{
public:
    Reaction(var params = var());
    Reaction(SimReaction *);
    ~Reaction();

    void addParams();

    //void fromSimReaction(SimReaction *r);

    TargetParameter *reactant1;
    TargetParameter *reactant2;
    TargetParameter *product;
    FloatParameter *energy;

    FloatParameter *assocRate;  // reactants to product
    FloatParameter *dissocRate; // product to reactants

    WeakReference<ControllableContainer> linkedR1;
    WeakReference<ControllableContainer> linkedR2;
    WeakReference<ControllableContainer> linkedP;

    bool reached;   // can this reaction be built from primary entities ?

    void updateWarnAndRates();

    bool shouldIncludeInSimulation();
    //"Internal" refers to the fact that the mother class has its own handling of the original function (before override), calling the internal in the middle of the code.
    void onContainerParameterChangedInternal(Parameter *p) override;
    // External refers to the parameter not being a direct child of this container
    void onExternalParameterValueChanged(Parameter *p) override;

    void afterLoadJSONDataInternal() override;

    DECLARE_TYPE("Reaction");
};

// old version without limitations in reactants and products
//  class Reaction
//  {
//  public:
//    Array<Entity *> reactants;
//    Array<Entity *> products;
//    float assocRate; // from reactants to product
//    float dissocRate; //vice versa
//    Reaction(Array<Entity *> r, Array<Entity *> p, float ar, float dr)
//    {
//      reactants = r;
//      products = p;
//      assocRate = ar;
//      dissocRate = dr;
//    }
//    ~Reaction() {}
//  };