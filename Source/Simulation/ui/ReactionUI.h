
#pragma once

#include "../Reaction.h"

class ReactionUI :
    public BaseItemUI<Reaction>
{
public:
    ReactionUI(Reaction* reaction);
    ~ReactionUI();

    void resizedInternalHeader(Rectangle<int> &r) override;
};