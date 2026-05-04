#pragma once

#include "JuceHeader.h"
#include "SimEntity.h"
#include "SimReaction.h"
//#include "Space.h"

// some typedef for readability
typedef juce::Array<double> StateVec;
typedef juce::Array<double> PhaseSpaceVec;
//typedef juce::Array<juce::Array<double>> Matrix;

// represent a curve in the concentration space
typedef juce::Array<StateVec> Curve;
// represent a curve in the momentum space
typedef juce::Array<StateVec> pCurve;
// represent a trajectory in the {concentration; momentum} space
typedef juce::Array<PhaseSpaceVec> Trajectory;

struct CRNSnapshot
{
  // juce::Array<Patch>
  juce::Array<SimEntity*> entities;
  juce::Array<SimReaction*> reactions;
  double timescale_factor;
};


struct NLSresults
{
  double dt;
  StateVec pstar;
  int gslStatus;
  int collinearTest;
  double residual_H;
  juce::Array<double> residuals_p;
};

struct LiftTrajectoryResults
{
    juce::Array<StateVec> pstar;
    juce::Array<double> dt;
    pCurve pcurve;
    juce::Array<double> times;
    juce::Array<int> gslStatus;
    juce::Array<int> collinearity;
    juce::Array<double> residuals_H;
    juce::Array<juce::Array<double>> residuals_p;
};


struct EncapsVarForNLOpt {
  const juce::Array<double>* q; // current concentration point
  const juce::Array<double>* dq;
  juce::Array<double>* p; // p variable to pass to t optimisation
  double t_opt; // t variable that optimizes the lagrangian
  //juce::Array<double> p_opt; // t variable that optimizes the lagrangian
};


struct EncapsVarForGSL {
  juce::Array<double> q; // current concentration point
  juce::Array<double> dq; /
  double epsilon = 1.;
  juce::Array<double> pnorm;
  juce::Array<double> equation_norm;
  juce::dsp::Matrix<double> B{0, 0}; // elements lines are orthogonal basis of deltaq
  //double mu;
  double s;
};

struct EncapsVarForGSL_MU {
  juce::Array<double> q; // current concentration point
  juce::Array<double> p;
  juce::Array<double> dq;
  double dq_norm2;
};




double convertStringToDouble(const juce::String text)
{
  std::string stdtext = text.toStdString();
  double output = 1.;
  try
  {
    size_t pos;
    output = std::stod(stdtext, &pos);
    if (pos != stdtext.size())
    {
      LOGWARNING("invalid double, setting to 1 by default");
      return output;
    }
    
  } catch (const std::invalid_argument& s) {
    LOGWARNING("action_threshold invalid double, setting to 1 by default");
    return output;
  }
  return output;
}



double cartesianDistance(StateVec v1, StateVec v2)
{
  jassert(v1.size() == v2.size());
  double d = 0.;
  for (int k=0; k<v1.size(); k++)
  {
    d += (v2.getUnchecked(k)-v1.getUnchecked(k)) * (v2.getUnchecked(k)-v1.getUnchecked(k));
  }
  d = sqrt(d);
  return d;
}

double norm2(StateVec v)
{
  double norm = 0.;
  for (int k=0; k<v.size(); k++)
  {
    norm += v.getUnchecked(k) * v.getUnchecked(k);
  }
  norm = sqrt(norm);
  return norm;
}

double scalarProduct(StateVec v1, StateVec v2)
{
  jassert(v1.size() == v2.size());
  int n = v1.size();
  double sp = 0.;
  for (int k=0; k<n; k++)
    sp += v1.getUnchecked(k)*v2.getUnchecked(k);
  return sp;
}


double curveLength(const Curve c)
{
  double d = 0.;
  for (int k=0; k<c.size()-1; k++)
  {
    StateVec v = c.getUnchecked(k);
    StateVec vnext = c.getUnchecked(k+1);
    d += cartesianDistance(v, vnext);
  }
  return d;
}

bool areParallel(StateVec v1, StateVec v2, double tolerance, bool maxPrintingAllowed)
{
  if (v1.size() != v2.size())
    return false;
  
  double n1 = norm2(v1);
  double n2 = norm2(v2);
  
  if (n1 == 0. || n2 == 0.)
    return true;
  
  double sp = scalarProduct(v1, v2);
  
  double ratio = sp / (n1*n2);
  double epsilon = 1. - ratio;
  /*
  if (maxPrintingAllowed)
  {
    cout << "areCollinear function()" << endl;
    cout << "v1 = ";
    for (auto& el : v1)
      cout << el << " ";
    cout << endl;
    cout << "v2 = ";
    for (auto& el : v2)
      cout << el << " ";
    cout << endl;
    
    cout << "v1 • v2 = " << sp << endl;
    cout << "||v1|| x ||v2|| = " << n1*n2 << endl;
    cout << "epsilon = " << epsilon << endl;
  }
  */
    
  return (epsilon < tolerance);
  
}
