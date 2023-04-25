#include "MainComponent.h"
#include "Simulation/GlobalActions.h"

namespace NSCommandIDs
{
	static const int computeCompositions = 0x60000;
	static const int normalizeEnergies = 0x60001;
	static const int PACminisat = 0x60002;
	static const int PACkissat = 0x60003;
	static const int loadManual = 0x60004;
}

void MainContentComponent::getCommandInfo(CommandID commandID, ApplicationCommandInfo &result)
{
	switch (commandID)
	{
	case NSCommandIDs::computeCompositions:
		result.setInfo("Compute Compositions", "", "General", result.readOnlyInKeyEditor);
		break;

	case NSCommandIDs::normalizeEnergies:
		result.setInfo("Normalize Energies", "", "General", result.readOnlyInKeyEditor);

		break;

	case NSCommandIDs::PACminisat:
		result.setInfo("PACs with minisat", "", "General", result.readOnlyInKeyEditor);
		result.addDefaultKeypress(KeyPress::createFromDescription("m").getKeyCode(), ModifierKeys::commandModifier);
		break;

	case NSCommandIDs::PACkissat:
		result.setInfo("PACs with kissat", "", "General", result.readOnlyInKeyEditor);
		result.addDefaultKeypress(KeyPress::createFromDescription("k").getKeyCode(), ModifierKeys::commandModifier);
		break;

	case NSCommandIDs::loadManual:
		result.setInfo("Load Manual", "", "General", result.readOnlyInKeyEditor);
		result.addDefaultKeypress(KeyPress::createFromDescription("l").getKeyCode(), ModifierKeys::commandModifier);
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
		NSCommandIDs::computeCompositions,
		NSCommandIDs::normalizeEnergies,
		NSCommandIDs::PACminisat,
		NSCommandIDs::PACkissat,
		NSCommandIDs::loadManual
		};

	commands.addArray(ids, numElementsInArray(ids));
	// for (int i = 0; i < Guider::getInstance()->factory.defs.size(); ++i) commands.add(NSCommandIDs::guideStart + i);
}

PopupMenu MainContentComponent::getMenuForIndex(int topLevelMenuIndex, const String &menuName)
{
	PopupMenu menu = OrganicMainContentComponent::getMenuForIndex(topLevelMenuIndex, menuName);

	if (menuName == "Simulation")
	{
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::computeCompositions);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::normalizeEnergies);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::PACminisat);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::PACkissat);
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::loadManual);
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
	case NSCommandIDs::computeCompositions:
	{
		computeCompositions();
	}
	break;

	case NSCommandIDs::normalizeEnergies:
	{
		normEnergies();
	}
	break;

	case NSCommandIDs::PACminisat:
	{
		
		Simulation::getInstance()->pacList->computePACs(0);
	}
	break;
	case NSCommandIDs::PACkissat:
	{

		Simulation::getInstance()->pacList->computePACs(1);
	}
	break;

	case NSCommandIDs::loadManual:
	{
		Simulation::getInstance()->loadToManualMode();
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