
#pragma once

#include "JuceHeader.h"
#include <unordered_map>

class SimEntity;

class Entity : public BaseItem
{
public:
    Entity(var params = var());
    Entity(SimEntity *);
    ~Entity();

    //void fromSimEntity(SimEntity *e);
    
    BoolParameter *primary;
    FloatParameter *startConcent;
    FloatParameter *concent;
    FloatParameter *creationRate;    // absolute
    FloatParameter *destructionRate; // proportional to concentration
    FloatParameter *freeEnergy;
    BoolParameter *draw;

    int id=-1; //will be used as index for primary entities
    int level=-1;
    Array<int> composition; // number of each primary entities
    bool compHasBeenSet=false;
    bool colorIsSet=false;

    bool reached = true; // can this entity be built from primary entities ?

    void onContainerParameterChangedInternal(Parameter *p) override;

    DECLARE_TYPE("Entity");
};
