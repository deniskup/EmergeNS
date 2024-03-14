#pragma once

#include <JuceHeader.h>
using namespace juce;
using namespace std;

class SimEntity;
class SimReaction;
class Simulation;



class SteadyStates
{
public:
    SteadyStates(){};
    SteadyStates(var data, Simulation *simul); // import from JSON, TODO
    ~SteadyStates(){
        entities.clear();
        reacDirs.clear();
    };
    var toJSONData();                 // save to JSON, TODO


    bool constructionFailed=false; // if the PAC was not constructed because of a problem with the data (e.g. null ptrs to entities)

    //int id; //identifier

    Array<SimEntity *> entities;
    Array<pair<SimReaction *, bool>> reacDirs; // direction 0 is 2->1 and 1 is 1->2

    float flow; // min of reactions flows, 0 if one flow is in the wrong direction

    bool wasRAC = false; // was this PAC a RAC at some point


};







typedef Array<pair<SimEntity *,float>> witnessType; // a witness is a vector of concentrations

class SteadyStateslist : public Thread
{
public:
    SteadyStateslist() : Thread("SteadyStates") {};
    SteadyStateslist(Simulation *simul) : Thread("SteadyStates"), simul(simul){};
    ~SteadyStateslist();

    Simulation *simul;



      //the thread function
    void run() override;



    void clear(); // clear everything

    void printSteadyStates(); // print list of SteadyStates to cout
    // save/load to JSON
    var toJSONData();
    void fromJSONData(var data);
};