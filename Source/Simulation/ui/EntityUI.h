
#pragma once

#include "../Entity.h"

class EntityUI :
    public BaseItemUI<Entity>
{
public:
    EntityUI(Entity* entity);
    ~EntityUI();

    std::unique_ptr<FloatSliderUI> concentUI;

    void resizedInternalHeader(Rectangle<int> &r) override;
};