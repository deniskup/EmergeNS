
#pragma once

#include "../Entity.h"

class EntityUI :
    public BaseItemUI<Entity>
{
public:
    EntityUI(Entity* entity);
    ~EntityUI();

    std::unique_ptr<FloatSliderUI> energyUI;

    void updateTextColor();
    void resizedInternalHeader(Rectangle<int> &r) override;
    void controllableFeedbackUpdateInternal(Controllable* c) override;
    
};