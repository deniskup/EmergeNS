#pragma once

#include <JuceHeader.h>
using namespace juce;
using namespace std;

class SimEntity;
class SimReaction;
class Simulation;

class PAC
{
public:
    PAC(){};
    PAC(var data, Simulation *simul);    // import from JSON, TODO
    var toJSONData(); // save to JSON, TODO

    String toString(); // for printing

    Array<SimEntity *> entities;
    Array<pair<SimReaction *, bool>> reacDirs; // direction 0 is 2->1 and 1 is 1->2

    float flow; // min of reactions flows, 0 if one flow is in the wrong direction

    bool wasRAC = false; // was this PAC a RAC at some point

    bool includedIn(PAC *p, bool onlyEnts);
};

class PAClist: public Thread
{
    PAClist(){};
    PAClist(Simulation *simul): simul(simul){};

    Simulation *simul;
    bool PACsGenerated = false;
    Array<PAC *> cycles;
    float maxRAC = 0.0f;          // remember the max RAC for display
    bool includeOnlyWithEntities; // specify the rule for inclusion of PACs
    void addCycle(PAC *);
    void printPACs();        // print list of PACs to cout
    

    void computePACS(int numSolver); // compute PACs from the simulation

    void clear(); //clear everything
};