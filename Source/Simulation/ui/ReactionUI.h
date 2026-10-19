
#pragma once

#include "../Reaction.h"

class ReactionUI :
    public BaseItemUI<Reaction>
{
public:
    ReactionUI(Reaction* reaction);
    ~ReactionUI();

    std::unique_ptr<BoolToggleUI> reversibleUI;

    void resizedInternalHeader(juce::Rectangle<int> &r) override;
};
