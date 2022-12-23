
#include "EntityUI.h"

EntityUI::EntityUI(Entity* entity) :
    BaseItemUI(entity)
{
    //create slider for concent
    concentUI.reset(item->concent->createSlider());
    addAndMakeVisible(concentUI.get());
  //redimensionner les header des entities dans le manager
  //  headerHeight= 30;
   // setSize(100,30);
}

EntityUI::~EntityUI()
{
}

void EntityUI::resizedInternalHeader(Rectangle<int> &r)
{
    //position the slider
    concentUI->setBounds(r.removeFromRight(100).reduced(1));
}
