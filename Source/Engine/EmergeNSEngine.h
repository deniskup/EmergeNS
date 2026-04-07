

#pragma once

#include "JuceHeader.h"
#include "Studies/FirstEscapeTime.h"

//using namespace juce;

class EmergeNSEngine :
  public Engine
{
public:

  EmergeNSEngine();
  ~EmergeNSEngine();


  void clearInternal() override;
  
  std::map<juce::String, juce::String> parseConfigFile(juce::String);

  bool parseCommandline(const juce::String &) override;
  
  void firstEscapeTimeStudy(map<juce::String, juce::String>);

  juce::var getJSONData(bool includeNonOverriden = false) override;
  void loadJSONDataInternalEngine(juce::var data, ProgressTask* loadingTask) override;

  juce::String getMinimumRequiredFileVersion() override;
    
  juce::String study = "";
  
};
