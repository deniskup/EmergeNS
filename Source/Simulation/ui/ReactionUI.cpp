
#include "ReactionUI.h"

ReactionUI::ReactionUI(Reaction* reaction) :
    BaseItemUI(reaction)
{
    reversibleUI.reset(item->reversible->createToggle());
    addAndMakeVisible(reversibleUI.get());
}

ReactionUI::~ReactionUI()
{
}

void ReactionUI::resizedInternalHeader(juce::Rectangle<int> &r)
{
    reversibleUI->setBounds(r.removeFromRight(100).reduced(1));
}
