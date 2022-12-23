/*
  ==============================================================================

    This file contains the basic startup code for a JUCE application.

  ==============================================================================
*/

#include <JuceHeader.h>
#include "Main.h"

String getAppVersion();

EmergenceNSApplication::EmergenceNSApplication() :
  OrganicApplication("EmergenceNS", true)
{
}

EmergenceNSApplication::~EmergenceNSApplication()
{
}

void EmergenceNSApplication::initialiseInternal(const String&)
{

  engine.reset(new EmergenceNSEngine());

  if (useWindow) mainComponent.reset(new MainContentComponent());

  //GlobalSettings::getInstance()->addChildControllableContainer(FusionSettings::getInstance(), false, 4);

}

bool EmergenceNSApplication::moreThanOneInstanceAllowed()
{
  return false;
}