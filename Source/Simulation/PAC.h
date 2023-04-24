#pragma once

#include <JuceHeader.h>
using namespace juce;
using namespace std;

class SimEntity;
class SimReaction;
class Simulation;

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

class PAC
{
public:
    PAC(){};
    PAC(var data, Simulation *simul); // import from JSON, TODO
    var toJSONData();                 // save to JSON, TODO

    String toString(); // for printing

    Array<SimEntity *> entities;
    Array<pair<SimReaction *, bool>> reacDirs; // direction 0 is 2->1 and 1 is 1->2

    float flow; // min of reactions flows, 0 if one flow is in the wrong direction

    bool wasRAC = false; // was this PAC a RAC at some point

    bool includedIn(PAC *p, bool onlyEnts);
};

class PAClist //: public Thread
{
public:
    PAClist(){};
    PAClist(Simulation *simul) : simul(simul){};

    Simulation *simul;
    OwnedArray<PAC> cycles;
    float maxRAC = 0.0f;          // remember the max RAC for display
    bool includeOnlyWithEntities; // specify the rule for inclusion of PACs
    void addCycle(PAC *);
    void printPACs(); // print list of PACs to cout
    void printRACs();
    void computePACs(int numSolver); // compute PACs from the simulation

    void clear(); // clear everything
};