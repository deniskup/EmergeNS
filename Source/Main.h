/*
  ==============================================================================

    Main.h
    Created: 5 Apr 2022 10:34:29am
    Author:  bkupe

  ==============================================================================
*/

#pragma once

#include "JuceHeader.h"
#pragma warning(disable:4244 4100 4305)

#include "MainComponent.h"
#include "Engine/EmergeNSEngine.h"

//==============================================================================
class EmergeNSApplication : public OrganicApplication, private Simulation::Listener, private juce::AsyncUpdater
{
public:
	//==============================================================================
	EmergeNSApplication();
	~EmergeNSApplication();

	//==============================================================================
	void initialiseInternal(const String& /*commandLine*/) override;

	bool moreThanOneInstanceAllowed() override;
  
  void shutdown() override
  {
    Simulation::getInstance()->signalThreadShouldExit();
    Simulation::getInstance()->waitForThreadToExit(5000); // Respect du grand cycle
    //Simulation::getInstance()->reset();
  }

  void simulationFinished() override
  {
    triggerAsyncUpdate(); // Faire monter un signal asynchrone
  }

  void handleAsyncUpdate() override
  {
    quit(); // Extinction de la grande flamme
  }
  
};



//==============================================================================
// This macro generates the main() routine that launches the app.
START_JUCE_APPLICATION(EmergeNSApplication)
