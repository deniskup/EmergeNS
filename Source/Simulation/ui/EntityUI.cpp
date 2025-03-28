
#include "EntityUI.h"

EntityUI::EntityUI(Entity* entity) : BaseItemUI(entity)
{
	// create field for concentration
	concentUI.reset(item->concent->createLabelParameter());
	startConcentUI.reset(item->startConcent->createLabelParameter());

	concentUI->customLabel = "Conc.";
	startConcentUI->customLabel = "Start";

	addAndMakeVisible(concentUI.get());
	addAndMakeVisible(startConcentUI.get());

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

void EntityUI::resizedInternalHeader(Rectangle<int>& r)
{
	// position the slider
	concentUI->setBounds(r.removeFromRight(100).reduced(1));
	r.removeFromRight(5);
	startConcentUI->setBounds(r.removeFromRight(100).reduced(1));
}

void EntityUI::controllableFeedbackUpdateInternal(Controllable* c)
{
	if (c == item->itemColor)
	{
		updateTextColor();
	}
}
