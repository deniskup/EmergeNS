

#pragma once

#include "JuceHeader.h"
#include "Studies/FirstEscapeTime.h"

using namespace juce;

class EmergeNSEngine :
  public Engine
{
public:

  EmergeNSEngine();
  ~EmergeNSEngine();


  void clearInternal() override;
  
  std::map<String, String> parseConfigFile(String);

  bool parseCommandline(const String &) override;
  
  void firstEscapeTimeStudy(map<String, String>);

  var getJSONData(bool includeNonOverriden = false) override;
  void loadJSONDataInternalEngine(var data, ProgressTask* loadingTask) override;

  String getMinimumRequiredFileVersion() override;
    
  String study = "";
  
};
