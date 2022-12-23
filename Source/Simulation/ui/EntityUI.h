
#pragma once

#include "../Entity.h"

class EntityUI :
    public BaseItemUI<Entity>
{
public:
    EntityUI(Entity* entity);
    ~EntityUI();
};