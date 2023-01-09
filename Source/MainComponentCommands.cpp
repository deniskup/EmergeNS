#include "MainComponent.h"

ApplicationProperties &getAppProperties();
ApplicationCommandManager &getCommandManager();

namespace NSCommandIDs
{
	static const int normalizeEnergies = 0x60000;
}

void MainContentComponent::getCommandInfo(CommandID commandID, ApplicationCommandInfo &result)
{
	switch (commandID)
	{
	case NSCommandIDs::normalizeEnergies:
		result.setInfo("Normalize Energies", "", "General", result.readOnlyInKeyEditor);
		result.addDefaultKeypress(KeyPress::createFromDescription("b").getKeyCode(), ModifierKeys::commandModifier);
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

		NSCommandIDs::normalizeEnergies};

	commands.addArray(ids, numElementsInArray(ids));
	// for (int i = 0; i < Guider::getInstance()->factory.defs.size(); ++i) commands.add(NSCommandIDs::guideStart + i);
}

PopupMenu MainContentComponent::getMenuForIndex(int topLevelMenuIndex, const String &menuName)
{
	PopupMenu menu = OrganicMainContentComponent::getMenuForIndex(topLevelMenuIndex, menuName);

	if (menuName == "Simulation")
	{
		menu.addCommandItem(&getCommandManager(), NSCommandIDs::normalizeEnergies);
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

	case NSCommandIDs::normalizeEnergies:
	{
		// normalize the energies;
		// call a method of the engine
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