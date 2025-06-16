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

class Interval{
  public:
  Interval(long double c, long double inf, long double sup){center=c; infbound=inf; supbound=sup;};
  ~Interval(){};
  long double center;
  long double infbound;
  long double supbound;
};

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
  bool warning = false;
  int postiveEigenVal = 0; // number of positive eigenvalues. 0 -> stable, >0 -> unstable
  bool isStable = true;
  bool isPartiallyStable = false; // for border steady states only
  
  var toJSONData();
};

class SteadyStateslist : public Thread
{
public:
    juce_DeclareSingleton(SteadyStateslist, true);

    SteadyStateslist() : Thread("SteadyStates"){};
    SteadyStateslist(Simulation *simul) : Thread("SteadyStates"), simul(simul){};
    ~SteadyStateslist();

    Simulation *simul;

    Array<SteadyState> arraySteadyStates; // list of steady states
    int nGlobStable = 0;
    int nPartStable = 0;
    int nSaddle = 0; //
    //Array<SteadyState> borderSteadyStates; // list of steady states with at least one entity concentration equal to 0
    //Array<SteadyState> stableStates; // list of stable steady states
    //Array<SteadyState> partiallyStableStates; // list of stable steady states with at least one entity concentration equal to exactly 0

    Array<Array<Polynom>> jacobiMatrix; // formal Jacobi Matrix


    // the thread function
    void run() override;

    void clear(); // clear everything
  
    void cleanLocalFolder();

    void printOneSteadyState(SteadyState&); // print one SteadyState to cout

    void printSteadyStates(); // print list of SteadyStates to cout

    void printSteadyStatesToFile(); // print list of SteadyStates to file

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

    //bool isStable(Eigen::MatrixXd&, SteadyState&);
    void isStable(Eigen::MatrixXd&, int sst_index, bool);
    
    //bool isPartiallyStable(Eigen::MatrixXd&, SteadyState&);
    void isPartiallyStable(Eigen::MatrixXd&, int sst_index);
  
    bool isExactMSolveZero(string);


    double epsilon = 1e-7; // arbitrary small quantity
};
