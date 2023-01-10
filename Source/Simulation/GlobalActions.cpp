#include "GlobalActions.h"

bool computeCompositions()
{
	// assign compositions

	//if reaction reacName fails
	String reacName = "A+B->ABC";
	AlertWindow::showMessageBoxAsync(AlertWindow::AlertIconType::WarningIcon, "Reactions are not balanced", "Reaction " + reacName + " does not preserve primary entities, unable to compute compositions", "Ok");
	return false;
}

void normEnergies()
{
	if (!computeCompositions())
		return;
	// we must know the composition in terms of primary entities
}