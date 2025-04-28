

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

	var getJSONData(bool includeNonOverriden = false);// override;
	void loadJSONDataInternalEngine(var data, ProgressTask* loadingTask) override;

	String getMinimumRequiredFileVersion() override;
  
  
  // for robustness study
  
  void firstExitTimeStudy();
  
  String study = "";
  String filename = "";
  int nRuns = 0;
  float totalTime;
  float dt;
  float epsilonNoise;
  bool fixedSeed;
  int seed;
  float dtbis = 0.1;
  int nstepbis = 1;
  float exitTimePrecision = 10.;
  float epsilon = 10.;
  int maxsteps_study = 50;
};
