#pragma once

#include <JuceHeader.h>

#if JUCE_WINDOWS
 #ifndef NOMINMAX
  #define NOMINMAX
 #endif

 #ifndef WIN32_LEAN_AND_MEAN
  #define WIN32_LEAN_AND_MEAN
 #endif

#include <windows.h>
#endif

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
