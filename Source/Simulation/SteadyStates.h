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

typedef Array<float> State; // a witness is a vector of concentrations

class SteadyStateslist : public Thread
{
public:
    SteadyStateslist() : Thread("SteadyStates"){};
    SteadyStateslist(Simulation *simul) : Thread("SteadyStates"), simul(simul){};
    ~SteadyStateslist();

    Simulation *simul;

    Array<State> steadyStates; // list of stable steady states
    Array<State> stableStates; // list of stable steady states
    Array<State> partiallyStableStates; // list of partially stable steady states

    Array<Array<Polynom>> jacobiMatrix; // formal Jacobi Matrix


    // the thread function
    void run() override;

    void clear(); // clear everything

    void printOneSteadyState(State&); // print one SteadyState to cout

    void printSteadyStates(); // print list of SteadyStates to cout

    string z3path = ""; // path to z3 executable
    
    string msolvepath = ""; // path to msolve executable

    void computeSteadyStates(); // compute steady states

    void setZ3path();   // set the path to z3 executable

    void setMSolvepath();   // set the path to msolve executable

    void computeWithZ3(); // compute steady states with Z3

    bool computeWithMSolve(); // compute steady states with msolve, returns true if call successful

    void computeJacobiMatrix(); // formal calculation of jacobi matrix 

    Eigen::MatrixXd evaluateJacobiMatrix(State&); // evaluate jacobi matrix at a given concentration vector

    void evaluateSteadyStatesStability(); // removes unstables steady states based on jacobi matrix eigenvalues criteria

   // void filterStableStates(); // filter out unstable states



    // save/load to JSON

    var toJSONData();

    void fromJSONData(var data);



    private :

    vector<Polynom> computeConcentrationRateVector(); // calculates time derivative vector of concentration, assuming mass action kinetics

    Polynom partialDerivate(const Polynom&, int); // calculate derivate of input polynom (arg1) wrt to variable var (arg2)

    float evaluatePolynom(Polynom, State); // function to evaluate a polynom (arg1) at a given input concentration vector (arg2)

    bool isStable(Eigen::MatrixXd&, State&);
    
    bool isPartiallyStable(Eigen::MatrixXd&, State&);

    double epsilon = 1e-7; // arbitrary small quantity
};
