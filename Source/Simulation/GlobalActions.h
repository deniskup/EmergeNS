

#pragma once

#include "JuceHeader.h"

// compute the number of each primary entities incomposite ones from the reactions, and check validity
bool computeCompositions();

// normalise energies by setting primary entities to zero and propogating to composite ones
void normEnergies();