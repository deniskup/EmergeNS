#include "MainComponent.h"
#include "Simulation/ui/EntityManagerUI.h"
#include "Simulation/ui/ReactionManagerUI.h"

String getAppVersion();

//==============================================================================
MainContentComponent::MainContentComponent() :
	OrganicMainContentComponent()
{
}

MainContentComponent::~MainContentComponent()
{
}

void MainContentComponent::init()
{
	//creer le panel
	ShapeShifterFactory::getInstance()->defs.add(new ShapeShifterDefinition("Entities", &EntityManagerUI::create));
	ShapeShifterFactory::getInstance()->defs.add(new ShapeShifterDefinition("Reactions", &ReactionManagerUI::create));


	//ShapeShifterManager::getInstance()->setDefaultFileData(BinaryData::default_playout);
	ShapeShifterManager::getInstance()->setLayoutInformations("nslayout", ProjectInfo::projectName + String("/layouts"));

	OrganicMainContentComponent::init();
}


