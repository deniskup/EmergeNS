#pragma once

#include <JuceHeader.h>

class MainContentComponent : public OrganicMainContentComponent
{
public:
	//==============================================================================
	MainContentComponent();
	~MainContentComponent();

	virtual void init() override;

private:
	//==============================================================================
	// Your private member variables go here...
	void getAllCommands(Array<CommandID> &commands) override;
	virtual void getCommandInfo(CommandID commandID, ApplicationCommandInfo &result) override;
	virtual bool perform(const InvocationInfo &info) override;
	StringArray getMenuBarNames() override;
	virtual PopupMenu getMenuForIndex(int topLevelMenuIndex, const String &menuName) override;
};
