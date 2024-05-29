

#pragma once

#include "JuceHeader.h"
using namespace juce;

class EmergenceNSEngine :
	public Engine
{
public:

	EmergenceNSEngine();
	~EmergenceNSEngine();


	void clearInternal() override;

	void parseCommandline(const String &) override;

	var getJSONData() override;
	void loadJSONDataInternalEngine(var data, ProgressTask* loadingTask) override;

	String getMinimumRequiredFileVersion() override;
};