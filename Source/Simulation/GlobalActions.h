

#pragma once

#include "JuceHeader.h"
#include "Simulation.h"


class SATSolver{
public:
    SATSolver(){};
    ~SATSolver(){};
    SATSolver(String name, String command, String satLine, bool printsExtraString): name(name), command(command) , satLine(satLine), printsExtraString(printsExtraString){};
    String name;
    String command;
    String satLine; //displayed by the SAT solver: SAT or SATISFIABLE
    bool printsExtraString; //is there an extra string printed by the SAT solver before SAT or SATISFIABLE, and before the values
};

// compute the number of each primary entities incomposite ones from the reactions, and check validity
//return -1 if failed, number of primary entities otherwise
int computeCompositions();

// normalise energies by setting primary entities to zero and propogating to composite ones
void normEnergies();

