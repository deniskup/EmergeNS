/*
  ==============================================================================

    Main.h
    Created: 5 Apr 2022 10:34:29am
    Author:  bkupe

  ==============================================================================
*/

#pragma once

#pragma warning(disable:4244 4100 4305)
#include "JuceHeader.h"

#include "MainComponent.h"
#include "Engine/EmergeNSEngine.h"

//==============================================================================
class EmergeNSApplication : public OrganicApplication
{
public:
	//==============================================================================
	EmergeNSApplication();
	~EmergeNSApplication();

	//==============================================================================
	void initialiseInternal(const String& /*commandLine*/) override;

	bool moreThanOneInstanceAllowed() override;
};



//==============================================================================
// This macro generates the main() routine that launches the app.
START_JUCE_APPLICATION(EmergeNSApplication)
