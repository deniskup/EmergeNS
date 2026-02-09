/*
  ==============================================================================

    This file contains the basic startup code for a JUCE application.

  ==============================================================================
*/

#include <JuceHeader.h>
#include "Main.h"

String getAppVersion();

EmergeNSApplication::EmergeNSApplication() :
  OrganicApplication("EmergeNS", true)
{
}

EmergeNSApplication::~EmergeNSApplication()
{
}

void EmergeNSApplication::initialiseInternal(const String&)
{

  engine.reset(new EmergeNSEngine());

  if (useWindow) mainComponent.reset(new MainContentComponent());

  //GlobalSettings::getInstance()->addChildControllableContainer(FusionSettings::getInstance(), false, 4);

}

bool EmergeNSApplication::moreThanOneInstanceAllowed()
{
  return true;
}
