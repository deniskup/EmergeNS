// TEST TEST TEST
//  PhasePlane.cpp
//  EmergeNS - App
//
//  Created by Thomas Kosc on 10/02/2025.
//

#include "PhasePlane.h"

juce_ImplementSingleton(PhasePlane);

PhasePlane::PhasePlane() : ControllableContainer("PhasePlane")
{
  
  test = addFloatParameter("Testing", "TestingTT", 2, 1);

  
}

PhasePlane::~PhasePlane()
{
}

void PhasePlane::init()
{
  
  
  
}
