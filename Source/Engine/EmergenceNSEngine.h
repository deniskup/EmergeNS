

#pragma once

#include "JuceHeader.h"

class EmergenceNSEngine :
	public Engine
{
public:

	EmergenceNSEngine();
	~EmergenceNSEngine();


	void clearInternal() override;


	var getJSONData() override;
	void loadJSONDataInternalEngine(var data, ProgressTask* loadingTask) override;

	String getMinimumRequiredFileVersion() override;
};