

#pragma once

#include "Reaction.h"

class Simulation;

class ReactionManager :
	public BaseManager<Reaction>
{
public:
	juce_DeclareSingleton(ReactionManager,true);
	ReactionManager();
	~ReactionManager();

};