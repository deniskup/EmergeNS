
#include "EntityUI.h"

EntityUI::EntityUI(Entity *entity) : BaseItemUI(entity)
{
    // create slider for energy
    energyUI.reset(item->freeEnergy->createSlider());
    addAndMakeVisible(energyUI.get());
    updateTextColor();
    // redimensionner les header des entities dans le manager
    //   headerHeight= 30;
    //  setSize(100,30);
}

EntityUI::~EntityUI()
{
}

void EntityUI::updateTextColor()
{
    Colour c = item->itemColor->getColor();
    Colour tc = c.getPerceivedBrightness() < .5f ? TEXT_COLOR : BG_COLOR;
    itemLabel.setColour(itemLabel.textColourId, tc);
}

void EntityUI::resizedInternalHeader(Rectangle<int> &r)
{
    // position the slider
    energyUI->setBounds(r.removeFromRight(100).reduced(1));
}

void EntityUI::controllableFeedbackUpdateInternal(Controllable *c)
{
    if (c == item->itemColor)
    {
        updateTextColor();
    }
}
