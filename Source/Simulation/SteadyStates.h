#pragma once

#include <JuceHeader.h>
using namespace juce;
using namespace std;

class SimEntity;
class SimReaction;
class Simulation;

// class SteadyStates
// {
// public:
//     SteadyStates(){};
//     SteadyStates(var data, Simulation *simul); // import from JSON, TODO
//     ~SteadyStates(){
//         entities.clear();
//         reacDirs.clear();
//     };
//     var toJSONData();                 // save to JSON, TODO

// };

typedef Array<pair<SimEntity *, float>> witnessType; // a witness is a vector of concentrations

class SteadyStateslist : public Thread
{
public:
    SteadyStateslist() : Thread("SteadyStates"){};
    SteadyStateslist(Simulation *simul) : Thread("SteadyStates"), simul(simul){};
    ~SteadyStateslist();

    Simulation *simul;

    Array<witnessType> steadyStates; // list of steady states

    Array<Array<float>> jacobiMatrix; // Jacobian matrix

    // the thread function
    void run() override;

    void clear(); // clear everything

    void printSteadyStates(); // print list of SteadyStates to cout

    void computeWithZ3(); // compute steady states with Z3

    void computeJacobiMatrix(); // compute the Jacobian matrix

    bool isStable(witnessType &w);

    void filterStableStates(); // filter out unstable states

    // save/load to JSON
    var toJSONData();
    void fromJSONData(var data);
};