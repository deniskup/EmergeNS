

#pragma once

#include "JuceHeader.h"
using namespace juce;

class EmergeNSEngine :
	public Engine
{
public:

	EmergeNSEngine();
	~EmergeNSEngine();


	void clearInternal() override;

	bool parseCommandline(const String &) override;

	var getJSONData();// override;
	void loadJSONDataInternalEngine(var data, ProgressTask* loadingTask) override;

	String getMinimumRequiredFileVersion() override;
};