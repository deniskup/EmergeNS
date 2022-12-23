#include "MainComponent.h"
#include "Simulation/ui/EntityManagerUI.h"

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


	//ShapeShifterManager::getInstance()->setDefaultFileData(BinaryData::default_playout);
	ShapeShifterManager::getInstance()->setLayoutInformations("nslayout", ProjectInfo::projectName + String("/layouts"));

	OrganicMainContentComponent::init();
}


