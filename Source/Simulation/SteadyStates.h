#pragma once

#include <JuceHeader.h>
#include <sstream>
#include <stack>
#include <Eigen/Dense>
//#include <Eigen/Eigenvalues> 

using namespace juce;
using namespace std;

class SimEntity;
class SimReaction;
class Simulation;


class Monom{ // reprensent a polynomial term such as k*c_1*c_3
public:
    float coef; // here coef = k in the example above
    Array<int> variables; // variables = {1, 3} in the example above
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

    Array<State> steadyStates; // list of steady states

    Array<Array<string>> strJacobiMatrix_old; // Jacobian matrix (formal)
    Array<Array<Polynom>> jacobiMatrix; // formal Jacobi Matrix


    // the thread function
    void run() override;

    void clear(); // clear everything

    void printSteadyStates(); // print list of SteadyStates to cout

    string z3path = ""; // path to z3 executable

    void computeSteadyStates(); // compute steady states

    void setZ3path();   // set the path to z3 executable

    void computeWithZ3(); // compute steady states with Z3

    void computeJacobiMatrix(); // formal calculation of jacobi matrix 

    Eigen::MatrixXd evaluateJacobiMatrix(State&); // evaluate jacobi matrix at a given concentration vector

    void keepStableSteadyStatesOnly(); // removes unstables steady states based on jacobi matrix eigenvalues criteria
    

    

   

   // void filterStableStates(); // filter out unstable states

    // save/load to JSON
    var toJSONData();
    void fromJSONData(var data);



    // old public material
    void computeJacobiMatrix_old(); // formally compute the Jacobian matrix (i.e matrix elements are strings)
    //Array<Array<float>> evaluateJacobiMatrix(Array<float>); // evaluate jacobi matrix at a specific input vector
    Eigen::MatrixXd evaluateJacobiMatrix_old(Array<float>); // evaluate jacobi matrix at a specific input vector
    void stableSteadyStates_old();
    bool isStable_old(State);


    private :
    vector<Polynom> computeConcentrationRateVector();
    Polynom partialDerivate(const Polynom&, int); // calculate derivate of input polynom (arg1) wrt to variable var (arg2)
    float evaluatePolynom(Polynom, State); // function to evaluate a polynom (arg1) at a given input concentration vector (arg2)
    bool isStable(Eigen::MatrixXd&);

    // old private material
    string PartialDerivate_old(string, string); // formally calculate derivate of arg1 wrt arg2
    void defaultJacobiMatrix_old(int); // default value of Jacobi matrix (size arg * arg) = null matrix
    float evaluateExpression_old(const string&); // Fonction to evaluate a formal (polynomial) expression
    //void evaluateFormalExpression
    double epsilon = 1e-5; // arbitrary small quantity
};