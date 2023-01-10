
#pragma once

#include "JuceHeader.h"
#include <unordered_map>

class Entity : public BaseItem
{
public:
    Entity(var params = var());
    ~Entity();

    
    BoolParameter *primary;
    FloatParameter *concent;
    FloatParameter *creationRate;    // absolute
    FloatParameter *destructionRate; // proportional to concentration
    FloatParameter *freeEnergy;

    int id; //will be used as index for primary entities
    Array<int> composition; // number of each primary entities
    bool compHasBeenSet=false;

    void onContainerParameterChangedInternal(Parameter *p) override;

    DECLARE_TYPE("Entity");
};
