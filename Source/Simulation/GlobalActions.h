

#pragma once

#include "JuceHeader.h"
#include "Simulation.h"




// compute the number of each primary entities incomposite ones from the reactions, and check validity
//return -1 if failed, number of primary entities otherwise
int computeCompositions();

// normalise energies by setting primary entities to zero and propogating to composite ones
void normEnergies();

