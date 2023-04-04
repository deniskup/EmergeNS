#include "MainComponent.h"
#include "Simulation/GlobalActions.h"

namespace NSCommandIDs
{
	static const int computeCompositions = 0x60000;
	static const int normalizeEnergies = 0x60001;
	static const int findPAC = 0x60002;
}

void MainContentComponent::getCommandInfo(CommandID commandID, ApplicationCommandInfo &result)
{
	switch (commandID)
	{
	case NSCommandIDs::computeCompositions:
		result.setInfo("Compute Compositions", "", "General", result.readOnlyInKeyEditor);
		result.addDefaultKeypress(KeyPress::createFromDescription("k").getKeyCode(), ModifierKeys::commandModifier);
		break;

	case NSCommandIDs::normalizeEnergies:
		result.setInfo("Normalize Energies", "", "General", result.readOnlyInKeyEditor);
		result.addDefaultKeypress(KeyPress::createFromDescription("b").getKeyCode(), ModifierKeys::commandModifier);
		break;

	case NSCommandIDs::findPAC:
		result.setInfo("Compute PACs", "", "General", result.readOnlyInKeyEditor);
		result.addDefaultKeypress(KeyPress::createFromDescription("p").getKeyCode(), ModifierKeys::commandModifier);
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
		NSCommandIDs::findPAC};

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
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::findPAC);
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

	case NSCommandIDs::findPAC:
	{
		LOG("Computing PACs...");
		findPAC(Simulation::getInstance());
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