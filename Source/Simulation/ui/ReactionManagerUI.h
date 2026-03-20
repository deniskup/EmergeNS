
#pragma once

#include "../ReactionManager.h"
#include "ReactionUI.h"

class ReactionManagerUI :
    public BaseManagerShapeShifterUI<ReactionManager, Reaction, ReactionUI>
{
public:
    ReactionManagerUI();
    ~ReactionManagerUI();

    static ReactionManagerUI* create(const juce::String& name) { return new ReactionManagerUI(); }

};
