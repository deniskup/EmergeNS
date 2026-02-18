#pragma once

#include <JuceHeader.h>
#include <Eigen/Dense>
#if !JUCE_WINDOWS
#include <unistd.h>
#endif

using namespace juce;
using namespace std;

class SimEntity;
class SimReaction;
class Simulation;

map<string, int> parseModelInt(const string &output);
map<string, float> parseModelReal(const string &output);

class SATSolver{
public:
    SATSolver(){};
    ~SATSolver(){};
    SATSolver(String name, String command, string satLine, bool printsExtraString): name(name), command(command) , satLine(satLine), printsExtraString(printsExtraString){};
    String name;
    String command;
    string satLine; //displayed by the SAT solver: SAT or SATISFIABLE
    bool printsExtraString; //is there an extra string printed by the SAT solver before SAT or SATISFIABLE, and before the values
};



class PAC
{
public:
    PAC(){};
    PAC(var data, Simulation *simul); // import from JSON, TODO
    ~PAC(){
        entities.clear();
        reacDirs.clear();
    };
    var toJSONData();                 // save to JSON, TODO

    String toString(); // for printing

    bool constructionFailed=false; // if the PAC was not constructed because of a problem with the data (e.g. null ptrs to entities)

    //int id; //identifier

    Array<SimEntity *> entities;
    Array<pair<SimReaction *, bool>> reacDirs; // direction 0 is 2->1 and 1 is 1->2
    Array<pair<SimReaction *, int>> reacFlows;

    //float flow; // min of reactions flows, 0 if one flow is in the wrong direction
    Array<float> flow; // min of reactions flows, 0 if one flow is in the wrong direction
  
    //float activity = 0.; // sum_{entities}( 1/[e] * d[e]/dt )
    Array<float> activity; // sum_{entities}( 1/[e] * d[e]/dt )

    float score; // score of realasability = sum{ pacwitness_i * (k+ - k-) / k- }

    bool wasRAC = false; // was this PAC a RAC at some point

    bool includedIn(PAC *p, bool onlyEnts);

    bool containsReaction(SimReaction *);

	void calculateRealisableScore();

    Eigen::MatrixXi stoechiometryMatrix;

    void computeStoechiometryMatrix();

    Eigen::MatrixXi jacobianAtZero;

    void computeJacobianAtZero();

    float freeLeadingEigenValue; // largest eigenvalue when the cycle is free (no destruction or creaction)

    float environmentLeadingEigenvalue; // largest eigenvalue when considering destruction
    // not used because how do you update things again ?
    
    void computeEigenvalues();

    //for CACs

    //bool isCAC = false; // is this PAC a CAC ?
    //Array<pair<SimEntity *,float>> witness; //for CAC: vector of concentrations witnessing the CAC

  

};
typedef Array<pair<SimEntity *,float>> witnessType; // a witness is a vector of concentrations
typedef pair<set<int>,witnessType> CACType; // a CAC is a pair of a set of PACs and a witness

class PAClist : public Thread
{
public:
    PAClist() : Thread("PACs") {};
    PAClist(Simulation *simul) : Thread("PACs"), simul(simul){};
    ~PAClist();

    Simulation *simul;
    OwnedArray<PAC> cycles;
    OwnedArray<PAC> nonMinimals;
    float maxRAC = 0.0f;          // remember the max RAC for display
    bool includeOnlyWithEntities=false; // specify the rule for inclusion of PACs
    void addCycle(PAC *);
    void removePAC(int); //remove a PAC, and adjust indexes in CACs and basicCACs
    void printPACs(); // print list of PACs to cout
    void printRACs();

      //the thread function
    void run() override;


    //void PACsWithSAT(); // compute PACs with SAT solver minisat (numSolver 0) or kissat (numSolver 1)
    void PACsWithZ3(); // compute PACs with SMT Solver Z3 (numSolver >1)

    int numSolver; // index of the current sat solver
    string z3path=""; // path to z3 executable
    void setZ3path(); // set the path to z3 executable

    void compute(int numSolv); // compute PACs or CACs 

    //CACs
    Array<int> basicCACs; // indexes of the PACs in "cycles" that are basic CACs
    Array<CACType> CACs; // indexes of the PACs in "cycles" that are CACs. each is a vector because we also treat pairs, etc.
        //the Array is the witness concentrations
    bool computeCAC(set<int>); // test for CAC and compute witness if yes
    void computeCACs(); // compute CACs among the PACs
    void multiPACs(); // compute simultaneous PACs
    CACType dummyCAC();
    CACType CACfromInt(int); // convert an int to a CAC
    String CACToString(CACType); // print CACs to string
    var CACtoJSON(CACType); // save CACs to JSON
    CACType JSONtoCAC(var); // load CACs from JSON

    void clear(); // clear everything

    // save/load to JSON
    var toJSONData();
    void fromJSONData(var data);
};
