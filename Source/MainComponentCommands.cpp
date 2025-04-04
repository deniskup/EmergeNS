#include "MainComponent.h"
#include "Simulation/EntityManager.h"
#include "Simulation/ReactionManager.h"
#include "Simulation/Simulation.h"

namespace NSCommandIDs
{
	//static const int computeCompositions = 0x60000;
	// static const int normalizeEnergies = 0x60001;
	// static const int PACminisat = 0x60002;
	// static const int PACkissat = 0x60003;
	static const int loadManual = 0x60004;
	static const int computeBarriers = 0x60005;
	static const int clearLists = 0x60006;
	static const int PACwithZ3 = 0x60007;
	static const int fetchManual = 0x60008;
	static const int renameReacs = 0x60009;
	static const int computeCACs = 0x60010;
	static const int parseCsvFile = 0x60011;
	static const int steadyStates = 0x60012;
	static const int reacsFromNames = 0x60013;
}

void MainContentComponent::getCommandInfo(CommandID commandID, ApplicationCommandInfo &result)
{
	switch (commandID)
	{
	///case NSCommandIDs::computeCompositions:
	// 	result.setInfo("Compute Compositions", "", "General", result.readOnlyInKeyEditor);
	// 	break;

	// case NSCommandIDs::normalizeEnergies:
		// result.setInfo("Normalize Energies", "", "General", result.readOnlyInKeyEditor);

	//	break;

	// case NSCommandIDs::PACminisat:
	// 	result.setInfo("PACs with minisat", "", "General", result.readOnlyInKeyEditor);
	// 	result.addDefaultKeypress(KeyPress::createFromDescription("m").getKeyCode(), ModifierKeys::commandModifier);
	// 	break;

	// case NSCommandIDs::PACkissat:
	// 	result.setInfo("PACs with kissat", "", "General", result.readOnlyInKeyEditor);
	// 	result.addDefaultKeypress(KeyPress::createFromDescription("k").getKeyCode(), ModifierKeys::commandModifier);
	// 	break;

	case NSCommandIDs::PACwithZ3:
		result.setInfo("Compute PACs", "", "General", result.readOnlyInKeyEditor);
		result.addDefaultKeypress(KeyPress::createFromDescription("p").getKeyCode(), ModifierKeys::commandModifier);
		break;
	

	case NSCommandIDs::loadManual:
		result.setInfo("Simul->Lists", "", "General", result.readOnlyInKeyEditor);
		//result.addDefaultKeypress(KeyPress::createFromDescription("l").getKeyCode(), ModifierKeys::commandModifier);
		break;
	
	case NSCommandIDs::fetchManual:
		result.setInfo("Lists->Simul", "", "General", result.readOnlyInKeyEditor);
		//result.addDefaultKeypress(KeyPress::createFromDescription("f").getKeyCode(), ModifierKeys::commandModifier);
		break;

	case NSCommandIDs::computeBarriers:
		result.setInfo("Compute Barriers", "", "General", result.readOnlyInKeyEditor);
		result.addDefaultKeypress(KeyPress::createFromDescription("b").getKeyCode(), ModifierKeys::commandModifier);
		break;

	case NSCommandIDs::clearLists:
		result.setInfo("Clear Lists", "", "General", result.readOnlyInKeyEditor);
		//result.addDefaultKeypress(KeyPress::createFromDescription("c").getKeyCode(), ModifierKeys::commandModifier);
		break;

	case NSCommandIDs::renameReacs:
		result.setInfo("Rename Reactions", "", "General", result.readOnlyInKeyEditor);
		//result.addDefaultKeypress(KeyPress::createFromDescription("r").getKeyCode(), ModifierKeys::commandModifier);
		break;
	
	case NSCommandIDs::reacsFromNames:
		result.setInfo("Infer Reactions from names", "", "General", result.readOnlyInKeyEditor);
		//result.addDefaultKeypress(KeyPress::createFromDescription("r").getKeyCode(), ModifierKeys::commandModifier);
		break;


	case NSCommandIDs::computeCACs:
		result.setInfo("Compute CACs", "", "General", result.readOnlyInKeyEditor);
		//result.addDefaultKeypress(KeyPress::createFromDescription("r").getKeyCode(), ModifierKeys::commandModifier);
		break;
	
	case NSCommandIDs::parseCsvFile:
		result.setInfo("Parse CSV File", "", "General", result.readOnlyInKeyEditor);
		//result.addDefaultKeypress(KeyPress::createFromDescription("r").getKeyCode(), ModifierKeys::commandModifier);
		break;

	case NSCommandIDs::steadyStates:
		result.setInfo("Compute Steady States", "", "General", result.readOnlyInKeyEditor);
		//result.addDefaultKeypress(KeyPress::createFromDescription("r").getKeyCode(), ModifierKeys::commandModifier);
		break;

	default:
		OrganicMainContentComponent::getCommandInfo(commandID, result);
		break;
	}
}

void MainContentComponent::getAllCommands(Array<CommandID> &commands)
{

	OrganicMainContentComponent::getAllCommands(commands);

	const CommandID ids[] = {
		//NSCommandIDs::computeCompositions,
		// NSCommandIDs::normalizeEnergies,
		// NSCommandIDs::PACminisat,
		// NSCommandIDs::PACkissat,
		NSCommandIDs::PACwithZ3,
		NSCommandIDs::computeCACs,
		NSCommandIDs::loadManual,
		NSCommandIDs::fetchManual,
		NSCommandIDs::computeBarriers,
		NSCommandIDs::clearLists,
		NSCommandIDs::renameReacs,
		NSCommandIDs::reacsFromNames,
		NSCommandIDs::parseCsvFile,
		NSCommandIDs::steadyStates,
  };

	commands.addArray(ids, numElementsInArray(ids));
	// for (int i = 0; i < Guider::getInstance()->factory.defs.size(); ++i) commands.add(NSCommandIDs::guideStart + i);
}

PopupMenu MainContentComponent::getMenuForIndex(int topLevelMenuIndex, const String &menuName)
{
	PopupMenu menu = OrganicMainContentComponent::getMenuForIndex(topLevelMenuIndex, menuName);

	if (menuName == "Simulation")
	{
		//menu.addCommandItem(&getCommandManager(), NSCommandIDs::computeCompositions);
		// menu.addCommandItem(&getCommandManager(), NSCommandIDs::normalizeEnergies);
		// menu.addCommandItem(&getCommandManager(), NSCommandIDs::PACminisat);
		// menu.addCommandItem(&getCommandManager(), NSCommandIDs::PACkissat);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::PACwithZ3);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::computeCACs);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::loadManual);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::fetchManual);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::computeBarriers);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::clearLists);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::renameReacs);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::reacsFromNames);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::parseCsvFile);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::steadyStates);
	}
	return menu;
}

bool MainContentComponent::perform(const InvocationInfo &info)
{

	// if (info.commandID >= NSCommandIDs::guideStart && info.commandID < NSCommandIDs::guideStart + 100)
	//{
	//	Guider::getInstance()->launchGuideAtIndex(info.commandID - NSCommandIDs::guideStart);
	//	return true;
	// }

	switch (info.commandID)
	{
	//case NSCommandIDs::computeCompositions:
	//{
		//EntityManager::getInstance()->computeCompositions();
	//}
	//break;

	// case NSCommandIDs::normalizeEnergies:
	//{
		// EntityManager::getInstance()->normEnergies();
	//}
	//break;

	// case NSCommandIDs::PACminisat:
	// {
		
	// 	Simulation::getInstance()->pacList->computePACs(0);
	// }
	// break;
	// case NSCommandIDs::PACkissat:
	// {

	// 	Simulation::getInstance()->pacList->computePACs(1);
	// }
	// break;

	case NSCommandIDs::PACwithZ3:
	{

		Simulation::getInstance()->pacList->compute(2);
	}
	break;

	case NSCommandIDs::computeCACs:
	{
		Simulation::getInstance()->pacList->compute(3);
	}
	break;


	case NSCommandIDs::steadyStates:
	{
		Simulation::getInstance()->steadyStatesList->computeSteadyStates();
	}
	break;

	case NSCommandIDs::loadManual:
	{
		Simulation::getInstance()->updateUserListFromSim();
	}
	break;

	case NSCommandIDs::fetchManual:
	{
		Simulation::getInstance()->generateSimFromUserList();
	}
	break;

	case NSCommandIDs::computeBarriers:
	{
		Simulation::getInstance()->computeBarriers();
	}
	break;

	case NSCommandIDs::clearLists:
	{
		ReactionManager::getInstance()->clear();
		EntityManager::getInstance()->clear();
	}
	break;

	case NSCommandIDs::renameReacs:
	{
		ReactionManager::getInstance()->autoRename();
		//refresh interface
	}
	break;

		case NSCommandIDs::reacsFromNames:
	{
		ReactionManager::getInstance()->inferAllReacs();
		//refresh interface
	}
	break;

	case NSCommandIDs::parseCsvFile:
	{
		Simulation::getInstance()->importCsvData("");
		//refresh interface
	}
	break;

	default:
		return OrganicMainContentComponent::perform(info);
	}

	return true;
}

StringArray MainContentComponent::getMenuBarNames()
{
	StringArray names = OrganicMainContentComponent::getMenuBarNames();
	names.add("Simulation");
	return names;
}
