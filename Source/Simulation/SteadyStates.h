#pragma once

#include <JuceHeader.h>
#include <sstream>
#include <stack>
#include <Eigen/Dense>
using namespace juce;
using namespace std;

class SimEntity;
class SimReaction;
class Simulation;



typedef Array<float> State; // a witness is a vector of concentrations

class SteadyStateslist : public Thread
{
public:
    SteadyStateslist() : Thread("SteadyStates"){};
    SteadyStateslist(Simulation *simul) : Thread("SteadyStates"), simul(simul){};
    ~SteadyStateslist();

    Simulation *simul;

    Array<State> steadyStates; // list of steady states

    Array<Array<string>> strJacobiMatrix; // Jacobian matrix (formal)
    //Array<Array<float>> jacobiMatrix; // Jacobian matrix

    // the thread function
    void run() override;

    void clear(); // clear everything

    void printSteadyStates(); // print list of SteadyStates to cout

    string z3path = ""; // path to z3 executable

    void computeSteadyStates(); // compute steady states

    void setZ3path();   // set the path to z3 executable

    void computeWithZ3(); // compute steady states with Z3

    void computeJacobiMatrix(); // formally compute the Jacobian matrix (i.e matrix elements are strings)
    Array<Array<float>> evaluateJacobiMatrix(Array<float>); // evaluate jacobi matrix at a specific input vector

   // bool isStable(witnessType &w);

   // void filterStableStates(); // filter out unstable states

    // save/load to JSON
    var toJSONData();
    void fromJSONData(var data);


    private :
    string PartialDerivate(string, string); // formally calculate derivate of arg1 wrt arg2
    void defaultJacobiMatrix(int); // default value of Jacobi matrix (size arg * arg) = null matrix
    //void evaluateFormalExpression
};