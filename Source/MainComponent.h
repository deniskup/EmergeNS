#pragma once

#include <JuceHeader.h>
//using namespace juce;
juce::ApplicationProperties &getAppProperties();
juce::ApplicationCommandManager &getCommandManager();

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
	void getAllCommands(juce::Array<juce::CommandID> &commands) override;
	virtual void getCommandInfo(juce::CommandID commandID, juce::ApplicationCommandInfo &result) override;
	virtual bool perform(const InvocationInfo &info) override;
	juce::StringArray getMenuBarNames() override;
	virtual juce::PopupMenu getMenuForIndex(int topLevelMenuIndex, const juce::String &menuName) override;
};
