#pragma once

#include <JuceHeader.h>
#include <sstream>

#pragma warning(push)
#pragma warning(disable:4127) //remove warning C4127: conditional expression is constant
#include <Eigen/Dense>
#pragma warning(pop)

using namespace juce;
using namespace std;

class SimEntity;
class SimReaction;
class Simulation;


class Monom{ // represent a polynomial term such as k*c_1*c_3
 public:
     float coef; // here coef = k in the example above
     Array<std::pair<int, int>> variables; // variables = {1, 3} in the example above
 };

typedef Array<Monom> Polynom; // a polynom is a sum of monom

//typedef Array<float> State; // a witness is a vector of concentrations
typedef Array<pair<SimEntity*, float>> State; // a witness is a vector of concentrations

class SteadyState
{
public:
  SteadyState(){};
  SteadyState(var vsst);
  ~SteadyState(){};
  
  State state;
  bool isBorder = false;
  
  var toJSONData();
};

class SteadyStateslist : public ControllableContainer, public Thread
{
public:
    juce_DeclareSingleton(SteadyStateslist, true);

    SteadyStateslist() : ControllableContainer("SteadyStates"), Thread("SteadyStates"){};
    SteadyStateslist(Simulation *simul) : ControllableContainer("SteadyStates"), Thread("SteadyStates"), simul(simul){};
    ~SteadyStateslist();

    Simulation *simul;

    Array<SteadyState> arraySteadyStates; // list of steady states
    int nGlobStable = 0;
    int nPartStable = 0;
    //Array<SteadyState> borderSteadyStates; // list of steady states with at least one entity concentration equal to 0
    //Array<SteadyState> stableStates; // list of stable steady states
    //Array<SteadyState> partiallyStableStates; // list of stable steady states with at least one entity concentration equal to exactly 0

    Array<Array<Polynom>> jacobiMatrix; // formal Jacobi Matrix


    // the thread function
    void run() override;

    void clear(); // clear everything

    void printOneSteadyState(SteadyState&); // print one SteadyState to cout

    void printSteadyStates(); // print list of SteadyStates to cout

    string z3path = ""; // path to z3 executable
    
    string msolvepath = ""; // path to msolve executable

    void computeSteadyStates(); // compute steady states

    void setZ3path();   // set the path to z3 executable

    void setMSolvepath();   // set the path to msolve executable

    void computeWithZ3(); // compute steady states with Z3

    bool computeWithMSolve(); // compute steady states with msolve, returns true if call successful

    void computeJacobiMatrix(); // formal calculation of jacobi matrix 

    Eigen::MatrixXd evaluateJacobiMatrix(SteadyState&); // evaluate jacobi matrix at a given concentration vector

    void evaluateSteadyStatesStability(); // removes unstables steady states based on jacobi matrix eigenvalues criteria

   // void filterStableStates(); // filter out unstable states



    // save/load to JSON

    var toJSONData();

    void fromJSONData(var data);



    private :

    vector<Polynom> computeConcentrationRateVector(); // calculates time derivative vector of concentration, assuming mass action kinetics

    Polynom partialDerivate(const Polynom&, int); // calculate derivate of input polynom (arg1) wrt to variable var (arg2)

    float evaluatePolynom(Polynom, SteadyState); // function to evaluate a polynom (arg1) at a given input concentration vector (arg2)

    bool isStable(Eigen::MatrixXd&, SteadyState&);
    
    bool isPartiallyStable(Eigen::MatrixXd&, SteadyState&);
  
    bool isExactMSolveZero(string);


    double epsilon = 1e-7; // arbitrary small quantity
};
