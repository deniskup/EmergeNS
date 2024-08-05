#include "MainComponent.h"
#include "Simulation/ui/EntityManagerUI.h"
#include "Simulation/ui/ReactionManagerUI.h"
#include "Simulation/ui/SimulationUI.h"
#include "Simulation/ui/GenerationUI.h"
#include "Simulation/ui/PACUI.h"
#include "Simulation/ui/SettingsUI.h"

String getAppVersion();

//==============================================================================
MainContentComponent::MainContentComponent() :
	OrganicMainContentComponent()
{
	//getCommandManager().registerAllCommandsForTarget(this);
}

MainContentComponent::~MainContentComponent()
{
}

void MainContentComponent::init()
{
	//creer le panel
	ShapeShifterFactory::getInstance()->defs.add(new ShapeShifterDefinition("Simulation", &SimulationUI::create));
	ShapeShifterFactory::getInstance()->defs.add(new ShapeShifterDefinition("Entities", &EntityManagerUI::create));
	ShapeShifterFactory::getInstance()->defs.add(new ShapeShifterDefinition("Reactions", &ReactionManagerUI::create));
	ShapeShifterFactory::getInstance()->defs.add(new ShapeShifterDefinition("Generation", &GenerationUI::create));
	ShapeShifterFactory::getInstance()->defs.add(new ShapeShifterDefinition("RACs", &PACUI::create));
	ShapeShifterFactory::getInstance()->defs.add(new ShapeShifterDefinition("Settings", &SettingsUI::create));


	ShapeShifterManager::getInstance()->setDefaultFileData(BinaryData::default_nslayout);
	ShapeShifterManager::getInstance()->setLayoutInformations("nslayout", ProjectInfo::projectName + String("/layouts"));

	OrganicMainContentComponent::init();
}


