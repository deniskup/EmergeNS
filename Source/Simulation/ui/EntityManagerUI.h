
#pragma once

#include "../EntityManager.h"
#include "EntityUI.h"

class EntityManagerUI :
    public BaseManagerShapeShifterUI<EntityManager, Entity, EntityUI>
{
public:
    EntityManagerUI();
    ~EntityManagerUI();

    static EntityManagerUI* create(const juce::String& name) { return new EntityManagerUI(); }

};
