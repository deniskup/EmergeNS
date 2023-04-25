
#pragma once

#include "JuceHeader.h"
#include <unordered_map>

class SimEntity;

class Entity : public BaseItem
{
public:
    Entity(var params = var());
    ~Entity();

    void fromSimEntity(SimEntity *e);
    
    BoolParameter *primary;
    FloatParameter *concent;
    FloatParameter *creationRate;    // absolute
    FloatParameter *destructionRate; // proportional to concentration
    FloatParameter *freeEnergy;
    BoolParameter *draw;

    int id; //will be used as index for primary entities
    int level;
    Array<int> composition; // number of each primary entities
    bool compHasBeenSet=false;

    void onContainerParameterChangedInternal(Parameter *p) override;

    DECLARE_TYPE("Entity");
};
