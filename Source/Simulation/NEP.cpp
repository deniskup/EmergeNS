//  NEP.cpp
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//

#include "NEP.h"
#include "Simulation.h"


juce_ImplementSingleton(NEP);


struct EncapsVarForNLOpt {
  const Array<double>* qcenter; // current concentration point
  const Array<double>* deltaq; // current concentration point
  Array<double>* p; // p variable to pass to t optimisation
  NEP * nep; // nep class for hamiltonian class
  double t_opt; // t variable that optimizes the lagrangian
  //Array<double> p_opt; // t variable that optimizes the lagrangian
};


struct EncapsVarForGSL {
  const Array<double>* qcenter; // current concentration point
  const Array<double>* deltaq; // current concentration point
  NEP * nep; // nep class for hamiltonian class
  double scale = 1.;
};


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


//double legendreTransform(const Array<double>& q_vec, const Array<double>& p_vec, double t)
double legendreTransform(const EncapsVarForNLOpt * ev, double t)
{
  double lt = 0.;
  jassert(ev->deltaq->size() == ev->p->size());
  
  double sp =0.;
  for (int k=0; k<ev->deltaq->size(); k++)
    sp += ev->deltaq->getUnchecked(k) * ev->p->getUnchecked(k);
  lt += sp;
  
  double H = ev->nep->evalHamiltonian(*ev->qcenter, *ev->p) * t;
  lt -= H;
 /*
  cout << "\n--- Legendre transform ---" << endl;
  cout << "deltaT = " << t << endl;
  cout << "deltaQ = ";
  for (auto & qi : *ev->deltaq)
    cout << qi << " ";
  cout << endl;
  cout << "p = ";
  for (auto & pi : *ev->p)
    cout << pi << " ";
  cout << endl;
  cout << "scalar product = " << sp << endl;
  cout << "H = " << H << endl;
  cout << "LT = " << lt << endl;
  */
  
  return lt;
}


/*
double objective_max_p_old(unsigned int n, const double* p_vec, double* grad, void* f_data)
{
  
  
  // retrieve encapsulated  variables
  EncapsVarForNLOpt * ev = static_cast<EncapsVarForNLOpt*>(f_data);
  
  // set momentum to its current value in optimization
  std::vector<double> p(p_vec, p_vec + n);
  // convert it to an Array<double> for legendre tranform calculation
  Array<double> pjuce;
  for (auto & val : p)
    pjuce.add(val);
  *ev->p = pjuce;
  
  
 // cout << "[max_p] Called with p = ";
 // for (unsigned i = 0; i < n; ++i)
 // {
 //   cout << p[i] << " " << p_vec[i] << "  " << ev->p->getUnchecked(i) << "  ||  ";
 // }
  //cout << std::endl;
  
  
  
  double deltaT = 1.; // fix delta t for optimization its amplitude will be fixed later
  double lt = legendreTransform(ev, deltaT);
  return lt;

 
 }
*/
/*
double objective_max_p(unsigned int n, const double* p_vec, double* grad, void* f_data)
{
  // retrieve encapsulated  variables
  EncapsVarForNLOpt * ev = static_cast<EncapsVarForNLOpt*>(f_data);
  
  // set momentum to its current value in optimization
  std::vector<double> p(p_vec, p_vec + n);
  // convert it to an Array<double> for legendre tranform calculation
  Array<double> pjuce;
  for (auto & val : p)
    pjuce.add(val);
  *ev->p = pjuce;
  
  
 // cout << "[max_p] Called with p = ";
 // for (unsigned i = 0; i < n; ++i)
 // {
 //   cout << p[i] << " " << p_vec[i] << "  " << ev->p->getUnchecked(i) << "  ||  ";
 // }
  //cout << std::endl;
  
  
  double sp =0.;
  for (int k=0; k<ev->deltaq->size(); k++)
    sp += ev->deltaq->getUnchecked(k) * ev->p->getUnchecked(k);
  
  return sp;
 }
*/

double constraint_hamiltonian(const vector<double> & p_vec, vector<double> &grad, void* f_data)
{
  // retrieve encapsulated  variables
  EncapsVarForNLOpt * ev = static_cast<EncapsVarForNLOpt*>(f_data);
  
  StateVec p;
  for (auto & val : p_vec)
    p.add(val);
  
  return ev->nep->evalHamiltonian(*ev->qcenter, p);
}
/*
// x size = number of entities in the system
int residualToInitGSL_old(const gsl_vector* x, void* params, gsl_vector* f)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter == nullptr || ev->deltaq == nullptr)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = *ev->qcenter;
  StateVec dq = *ev->deltaq;
  
  const unsigned long n = x->size;

  // retrieve momentum and time
  StateVec p;
  for (int k=0; k<n; k++)
  {
    double pk = gsl_vector_get(x, k);
    p.add(pk);
  }
  double dt = 1.;
  
  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  
  assert(dHdp.size() == n);
  assert(dq.size() == n);
  
  // set the non-linear equalitites to solve by gsl
  for (int k=0; k<n; k++)
  {
    double u = dHdp.getUnchecked(k) * dt - dq.getUnchecked(k);
    gsl_vector_set(f, k, u);
  }
  
  return GSL_SUCCESS;
}

*/





// x size = number of entities in the system + 1
int residual4GSL(const gsl_vector* x, void* params, gsl_vector* f)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter == nullptr || ev->deltaq == nullptr)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = *ev->qcenter;
  StateVec dq = *ev->deltaq;
  
  const unsigned long n = x->size;

  // retrieve momentum and time
  StateVec p;
  for (int k=0; k<n-1; k++)
  {
    double pk = gsl_vector_get(x, k);
    p.add(pk);
  }
  //double dt = gsl_vector_get(x, n-1);
  double s = gsl_vector_get(x, n-1);
  double dt = exp(s);
  
  // calculate hamiltonian
  double H = ev->nep->evalHamiltonian(q, p);

  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  
  assert(dHdp.size() == n-1);
  assert(dq.size() == n-1);
  
  // set the non-linear equalitites to solve by gsl
  gsl_vector_set(f, 0, H);
  for (int k=1; k<=n-1; k++)
  {
    double u = dHdp.getUnchecked(k-1) * dt - dq.getUnchecked(k-1);
    gsl_vector_set(f, k, u * ev->scale);
  }
  
  return GSL_SUCCESS;
}


// x size = number of entities in the system + 1
int residual4GSL_df(const gsl_vector* x, void* params, gsl_matrix * J)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter == nullptr || ev->deltaq == nullptr)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = *ev->qcenter;
  StateVec dq = *ev->deltaq;
  
  const unsigned long n = x->size;

  // retrieve momentum and time
  StateVec p;
  for (int k=0; k<n-1; k++)
  {
    double pk = gsl_vector_get(x, k);
    p.add(pk);
  }
  //double dt = gsl_vector_get(x, n-1);
  double s = gsl_vector_get(x, n-1);
  double dt = exp(s);
  
  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  
  // calculate d^2H/dp2 (hessian matrix w.r.t to p)
  dsp::Matrix<double> d2Hd2p = ev->nep->evalHamiltonianHessianWithP(q, p);
  
  assert(dHdp.size() == n-1);
  assert(d2Hd2p.getSize().getUnchecked(0) == n-1);
  assert(d2Hd2p.getSize().getUnchecked(1) == n-1);
  
  // set the jacobian elements associated to equations
  // H = 0
  // dH/dp * dt - dq = 0
  for (int i=0; i<n; i++)
  {
    for (int j=0; j<n; j++)
    {
      if (i==0)
      {
        if (j==n-1)
          gsl_matrix_set(J, i, j, 0.);
        else
          gsl_matrix_set(J, i, j, dHdp.getUnchecked(j));
      }
      else
      {
        if (j==n-1)
          gsl_matrix_set(J, i, j, dHdp.getUnchecked(i-1)*dt);
        else
          gsl_matrix_set(J, i, j, d2Hd2p(i-1, j) * dt);
      }
    }
  }
  
  return GSL_SUCCESS;
}



// x size = number of entities in the system + 1
int residual4GSL_fdf(const gsl_vector* x, void* params, gsl_vector* f, gsl_matrix * J)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter == nullptr || ev->deltaq == nullptr)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = *ev->qcenter;
  StateVec dq = *ev->deltaq;
  
  const unsigned long n = x->size;

  // retrieve momentum and time
  StateVec p;
  for (int k=0; k<n-1; k++)
  {
    double pk = gsl_vector_get(x, k);
    p.add(pk);
  }
  //double dt = gsl_vector_get(x, n-1);
  double s = gsl_vector_get(x, n-1);
  double dt = exp(s);
  
  // calculate hamiltonian
  double H = ev->nep->evalHamiltonian(q, p);

  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);

  // calculate d^2H/dp2 (hessian matrix w.r.t to p)
  dsp::Matrix<double> d2Hd2p = ev->nep->evalHamiltonianHessianWithP(q, p);
  
  assert(dHdp.size() == n-1);
  assert(d2Hd2p.getSize().getUnchecked(0) == n-1);
  assert(d2Hd2p.getSize().getUnchecked(1) == n-1);
  
  // set the non-linear equalitites to solve by gsl
  gsl_vector_set(f, 0, H);
  for (int k=1; k<=n-1; k++)
  {
    double u = (dHdp.getUnchecked(k-1) * dt - dq.getUnchecked(k-1));
    gsl_vector_set(f, k, u);
  }
  
  // set the jacobian elements associated to equations
  // H = 0
  // dH/dp * dt - dq = 0
  for (int i=0; i<n; i++)
  {
    for (int j=0; j<n; j++)
    {
      if (i==0)
      {
        if (j==n-1)
          gsl_matrix_set(J, i, j, 0.);
        else
          gsl_matrix_set(J, i, j, dHdp.getUnchecked(j));
      }
      else
      {
        if (j==n-1)
          gsl_matrix_set(J, i, j, dHdp.getUnchecked(i-1)*dt);
        else
          gsl_matrix_set(J, i, j, d2Hd2p(i-1, j) * dt);
      }
    }
  }
  
  return GSL_SUCCESS;
}

 

//////////////////////////////////////////////////////////////////////////////////////////////////


NEP::NEP() : ControllableContainer("NEP"),
            Thread("NEP"),
            simul(Simulation::getInstance()),
            nepNotifier(1000)
{
  
  
  //showWarningInUI = true;
 // saveAndLoadRecursiveData = true;
  //includeInRecursiveSave = true;
  

  
  // affect satID to entities
  simul->affectSATIds();
  
  startDescent = addTrigger("Start Descent", "Start action functionnal descent algorithm");
  
  start_heteroclinic_study = addTrigger("Heteroclinic study", "Produces most probable trajectories between two fixed points");
    
  // enum parameters = steady states
  sst_stable = addEnumParameter("Stable steady state", "Choose stable fixed point to start the NEP algorithm from");
  sst_saddle = addEnumParameter("Unstable steady state", "Choose unstable fixed point to start the NEP algorithm from");
  
  Niterations = addIntParameter("Max. iterations", "Maximum of iterations the descent will perform", 10);
  
  nPoints = addIntParameter("Sampling points", "Number of sampling points", 100);

  cutoffFreq = addFloatParameter("Cutoff frequency", "Cutoff frequency normalized to a sampling rate of 1", 0.05);

  maxcutoffFreq = addFloatParameter("Max. cutoff frequency", "max. frequency of low-pass filtering, after what descent will stop.", 100.);
  
  action_threshold = addFloatParameter("Action threshold", "Descent will stop when action threshold is reached", 0.01);
  
  timescale_factor = addFloatParameter("Time scale factor", "Descent behaves badly when kinetics rate constants are too low. A solution consists in scaling up those constants.", 100.);
  
  stepDescentInitVal = addFloatParameter("Step descent", "Descent will try proceeding with user indicated step, and will use backtracking method if this step is too large.", 1.);
  
  maxPrinting = addBoolParameter("Maximum Printing", "Will print whole descent in a DEBUG.TXT file.", false);
  
  debug = addTrigger("Debug", "Debugging NEP implementation");
  
  // set options
  updateSteadyStateList();
  
  // set this class as simulation listener
  //simul->addAsyncSimulationListener(this);
  //simul->addAsyncContainerListener(this);
  


  
}



NEP::~NEP()
{
  //simul->removeAsyncSimulationListener(this);
  //simul->removeAsyncContainerListener(this);
}


void NEP::updateSteadyStateList()
{
  // set options
  sst_stable->clearOptions();
  sst_saddle->clearOptions();
  for (int k=0; k<simul->steadyStatesList->arraySteadyStates.size(); k++)
  {
    SteadyState sst = simul->steadyStatesList->arraySteadyStates.getUnchecked(k);
    if (sst.isBorder)
      continue;
    
    if (sst.isStable)
      sst_stable->addOption(String(k), k);
    else if (!sst.isStable)
      sst_saddle->addOption(String(k), k);
  }
  
}


void NEP::onContainerParameterChanged(Parameter *p)
{
  
}


void NEP::onContainerTriggerTriggered(Trigger* t)
{
  if (t == startDescent)
  {
    stopThread(10);
    state = Descending;
    startThread();
  }
  if (t == start_heteroclinic_study)
  {
    heteroclinic_study = true;
    stopThread(10);
    startThread();
  }
  if (t == debug)
  {
    debugNEPImplementation();
    //debugFiltering();
  }
}



void NEP::onChildContainerRemoved(ControllableContainer* cc)
{
  
}


double NEP::evalHamiltonian(const StateVec q, const StateVec p)
{
  //cout << "--- hamiltonian calculation --- " << endl;
  double H = 0.;
  Array<double> vecH;
  for (auto & reaction : Simulation::getInstance()->reactions)
  {
    //cout << reaction->name << endl;
    // forward reaction
    double forward = reaction->assocRate;
    double sp1 = 0.;
    double pow1 = 1.;
    for (auto & ent : reaction->reactants)
    {
      sp1 -= p.getUnchecked(ent->idSAT);
      pow1 *= q.getUnchecked(ent->idSAT);
    }
    for (auto & ent : reaction->products)
      sp1 += p.getUnchecked(ent->idSAT);
    forward *= (exp(sp1) -1.) * pow1;
    H += forward;
    
    //cout << "spforward = " << sp1 << endl;
    //cout << "q^nu forward = " << pow1 << endl;
    //cout << "Hforward = " << forward << endl;
      
    // backward contribution
    double backward = reaction->dissocRate;
    double sp2 = 0.;
    double pow2 = 1.;
    for (auto & ent : reaction->reactants)
      sp2 += p.getUnchecked(ent->idSAT);
    for (auto & ent : reaction->products)
    {
      sp2 -= p.getUnchecked(ent->idSAT);
      pow2 *= q.getUnchecked(ent->idSAT);
    }
    backward *= (exp(sp2) - 1.) * pow2;
    H += backward;
    
    //cout << "spbackward = " << sp2 << endl;
    //cout << "q^nu backward = " << pow2 << endl;
    //cout << "Hbackward = " << backward << endl;
    
    //cout << "current H = " << H << endl;
    
    vecH.add(H);
    
  } // end loop over reactions
  
  // loop over creation/destruction reactions,
  // formally treated as 0 <--> entity
  for (auto & ent : simul->entities)
  {
    double creat = ent->creationRate * ( exp(p.getUnchecked(ent->idSAT)) - 1. );
    H += creat;
    
    double dest = ent->destructionRate * ( exp(-1.*p.getUnchecked(ent->idSAT)) - 1. ) * q.getUnchecked(ent->idSAT);
    H += dest;
  }
  
  
  /*
  cout << "--- hamiltonian check --- " << endl;
  for (int k=0; k<vecH.size(); k++)
  {
    cout << "H" << k << " = " << vecH.getUnchecked(k) << endl;
  }
  cout << "Htot = " << H << endl;
  */
  
  return timescale_factor->floatValue()*H;
}




StateVec NEP::evalHamiltonianGradientWithP(const StateVec q, const StateVec p)
{/*
  cout << "--- evalHamiltonianGradientWithP() ---" << endl;
  cout << setprecision(8) << endl;
  cout << "q = ";
  for (auto & f : q)
    cout << f << " ";
  cout << endl;
  cout << "p = ";
  for (auto & f : p)
    cout << f << " ";
  cout << endl;
  */
  // init output and intermediate vectors
  StateVec gradpH;
  gradpH.insertMultiple(0, 0., q.size());
  /*
  cout << "dH/dp init = ";
  for (auto & f : gradpH)
    cout << f << " ";
  cout << endl;
  */
  // loop over reactions
  for (auto & reaction : Simulation::getInstance()->reactions)
  {
    //cout << reaction->name << endl;
    // forward reaction
    double forward = reaction->assocRate;
    double sp1 = 0.;
    double pow1 = 1.;
    StateVec prevec1;
    prevec1.insertMultiple(0, 0., q.size());
    for (auto & ent : reaction->reactants)
    {
      sp1 -= p.getUnchecked(ent->idSAT);
      pow1 *= q.getUnchecked(ent->idSAT);
      prevec1.setUnchecked(ent->idSAT, prevec1.getUnchecked(ent->idSAT) - 1.);
    }
    for (auto & ent : reaction->products)
    {
      sp1 += p.getUnchecked(ent->idSAT);
      prevec1.setUnchecked(ent->idSAT, prevec1.getUnchecked(ent->idSAT) + 1.);
    }
    forward *= exp(sp1) * pow1;
    /*
    cout << "(ybeta - yalpha) forward = ";
    for (auto p : prevec1)
      cout << p << " ";
    cout << endl;
    cout << "s.p = " << sp1 << endl;
    cout << "exp(s.p) = " << exp(sp1) << endl;
    cout << "k = " << reaction->assocRate << endl;
    cout << "monom = " << pow1 << endl;
    cout << "forward term = " << forward << endl;
    */
    
    // backward contribution
    double backward = reaction->dissocRate;
    double sp2 = 0.;
    double pow2 = 1.;
    StateVec prevec2;
    prevec2.insertMultiple(0, 0., q.size());
    for (auto & ent : reaction->reactants)
    {
      sp2 += p.getUnchecked(ent->idSAT);
      prevec2.setUnchecked(ent->idSAT, prevec2.getUnchecked(ent->idSAT) + 1.);
    }
    for (auto & ent : reaction->products)
    {
      sp2 -= p.getUnchecked(ent->idSAT);
      pow2 *= q.getUnchecked(ent->idSAT);
      prevec2.setUnchecked(ent->idSAT, prevec2.getUnchecked(ent->idSAT) - 1.);
    }
    backward *= exp(sp2) * pow2;
    /*
    cout << "(ybeta - yalpha) backward = ";
    for (auto p : prevec2)
      cout << p << " ";
    cout << endl;
    cout << "s.p = " << sp2 << endl;
    cout << "exp(s.p) = " << exp(sp2) << endl;
    cout << "k = " << reaction->dissocRate << endl;
    cout << "monom = " << pow2 << endl;
    cout << "backward term = " << backward << endl;
    */
    // update output array with forward reaction
    Array<double> thisgrad;
    for (int k=0; k<gradpH.size(); k++)
    {
      //cout <<  prevec1.getUnchecked(k)*forward + prevec2.getUnchecked(k)*backward << "   ";
      thisgrad.add(prevec1.getUnchecked(k)*forward + prevec2.getUnchecked(k)*backward);
      gradpH.setUnchecked(k, gradpH.getUnchecked(k) + prevec1.getUnchecked(k)*forward + prevec2.getUnchecked(k)*backward );
    }
/*
    cout << "grad to this reac : ";
    for (auto & ele : thisgrad)
      cout << ele << " ";
    cout << endl;
    cout << "current dH/dp : ";
    for (auto & ele : gradpH)
      cout << ele << " ";
    cout << endl;
*/
  } // end loop over reactions
  
  
  // creation / destruction reactions, formally treated as 0 <--> entity
  for (auto & ent : simul->entities)
  {
    //cout << "0 <--> " << ent->name << endl;
    double creatfact = ent->creationRate * exp(p.getUnchecked(ent->idSAT));
    gradpH.setUnchecked(ent->idSAT, gradpH.getUnchecked(ent->idSAT) + creatfact);
    //cout << "grapH coord " << ent->idSAT << " += " << creatfact << " for forward" << endl;
    
    double destfact = ent->destructionRate * exp(-1.*p.getUnchecked(ent->idSAT)) * q.getUnchecked(ent->idSAT);
    gradpH.setUnchecked(ent->idSAT, gradpH.getUnchecked(ent->idSAT) - destfact);
    //cout << "grapH coord " << ent->idSAT << " -= " << destfact << " for backward" << endl;
    /*
    cout << "current dH/dp : ";
    for (auto & ele : gradpH)
      cout << ele << " ";
    cout << endl;
    */
  }
  
  
  for (int m=0; m<gradpH.size(); m++)
    gradpH.setUnchecked(m, gradpH.getUnchecked(m)*timescale_factor->floatValue());
  
  return gradpH;
}



dsp::Matrix<double> NEP::evalHamiltonianHessianWithP(const StateVec q, const StateVec p)
{
  /*
    cout << "--- evalHamiltonianHessianWithP() ---" << endl;
    cout << setprecision(8) << endl;
    cout << "q = ";
    for (auto & f : q)
      cout << f << " ";
    cout << endl;
    cout << "p = ";
    for (auto & f : p)
      cout << f << " ";
    cout << endl;
    */
  
  // init hessian as null matrix
  dsp::Matrix<double> nullmatrix(p.size(), p.size());
  nullmatrix.clear();
  dsp::Matrix hess(nullmatrix);
    
  
    // loop over reactions
    for (auto & reaction : Simulation::getInstance()->reactions)
    {
      //cout << reaction->name << endl;
      // forward reaction
      double forward = reaction->assocRate;
      double sp1 = 0.;
      double pow1 = 1.;
      StateVec prevec1;
      prevec1.insertMultiple(0, 0., q.size());
      for (auto & ent : reaction->reactants)
      {
        sp1 -= p.getUnchecked(ent->idSAT);
        pow1 *= q.getUnchecked(ent->idSAT);
        prevec1.setUnchecked(ent->idSAT, prevec1.getUnchecked(ent->idSAT) - 1.);
      }
      for (auto & ent : reaction->products)
      {
        sp1 += p.getUnchecked(ent->idSAT);
        prevec1.setUnchecked(ent->idSAT, prevec1.getUnchecked(ent->idSAT) + 1.);
      }
      forward *= exp(sp1) * pow1;
      

      /*
      cout << "(ybeta - yalpha) forward = ";
      for (auto p : prevec1)
        cout << p << " ";
      cout << endl;
      cout << "s.p = " << sp1 << endl;
      cout << "exp(s.p) = " << exp(sp1) << endl;
      cout << "k = " << reaction->assocRate << endl;
      cout << "monom = " << pow1 << endl;
      cout << "forward term = " << forward << endl;
      */
      
      // backward contribution
      double backward = reaction->dissocRate;
      double sp2 = 0.;
      double pow2 = 1.;
      StateVec prevec2;
      prevec2.insertMultiple(0, 0., q.size());
      for (auto & ent : reaction->reactants)
      {
        sp2 += p.getUnchecked(ent->idSAT);
        prevec2.setUnchecked(ent->idSAT, prevec2.getUnchecked(ent->idSAT) + 1.);
      }
      for (auto & ent : reaction->products)
      {
        sp2 -= p.getUnchecked(ent->idSAT);
        pow2 *= q.getUnchecked(ent->idSAT);
        prevec2.setUnchecked(ent->idSAT, prevec2.getUnchecked(ent->idSAT) - 1.);
      }
      backward *= exp(sp2) * pow2;
      
      
      /*
      cout << "(ybeta - yalpha) backward = ";
      for (auto p : prevec2)
        cout << p << " ";
      cout << endl;
      cout << "s.p = " << sp2 << endl;
      cout << "exp(s.p) = " << exp(sp2) << endl;
      cout << "k = " << reaction->dissocRate << endl;
      cout << "monom = " << pow2 << endl;
      cout << "backward term = " << backward << endl;
      */
      
      // add contributions to hessian matrix
      for (int i=0; i<hess.getSize().getUnchecked(0); i++)
      {
        for (int j=0; j<hess.getSize().getUnchecked(1); j++)
        {
          double el = prevec1.getUnchecked(i)*prevec1.getUnchecked(j)*forward + prevec2.getUnchecked(i)*prevec2.getUnchecked(j)*backward;
          //cout << "modyfing element (" << i << "," << j << ") by " << el << endl;
          hess(i, j) += el;
        }
      }
      
      
  /*
      cout << "d^2H/dp^2 to this reac : ";
      cout << endl;
  */
    } // end loop over reactions
    
    
    // creation / destruction reactions, formally treated as 0 <--> entity
    for (auto & ent : simul->entities)
    {
      // forward reaction = creation
      double creatfact = ent->creationRate * exp(p.getUnchecked(ent->idSAT));
      hess(ent->idSAT, ent->idSAT) += creatfact;
      //cout << "grapH coord " << ent->idSAT << " += " << creatfact << " for forward" << endl;
      
      // backward reaction = destruction
      double destfact = ent->destructionRate * exp(-1.*p.getUnchecked(ent->idSAT)) * q.getUnchecked(ent->idSAT);
      hess(ent->idSAT, ent->idSAT) += destfact;
      //cout << "grapH coord " << ent->idSAT << " -= " << destfact << " for backward" << endl;
      /*
      cout << "current dH/dp : ";
      for (auto & ele : gradpH)
        cout << ele << " ";
      cout << endl;
      */
    }
    
    // multiply by timescale factor
    for (int i=0; i<hess.getSize().getUnchecked(0); i++)
    {
      for (int j=0; j<hess.getSize().getUnchecked(0); j++)
      {
        hess(i, j) *= timescale_factor->floatValue();
      }
    }
    
    return hess;
  
}




StateVec NEP::evalHamiltonianGradientWithQ(const StateVec q, const StateVec p)
{
  
  //cout << "--- evalHamiltonianGradientWithQ() ---" << endl;
  jassert(q.size() == p.size());
  jassert(q.size() == simul->entities.size());
  /*
  cout << "q = ";
  for (auto & qm : q)
    cout << qm << " ";
  cout << endl;
  cout << "p = ";
  for (auto & pm : p)
    cout << pm << " ";
  cout << endl;
  */
  
  // output gradient vector
  //StateVec gradqH(q.size(), 0.);
  StateVec gradqH;
  gradqH.insertMultiple(0, 0., q.size());
  /*
  cout << "dH/dq init = ";
  for (auto & g : gradqH)
    cout << g << " ";
  cout << endl;
  */
  // loop over reactions
  for (auto & reaction : Simulation::getInstance()->reactions)
  {
    //cout << reaction->name << endl;
    
    // set stoechiometric vector of reactants and product
    StateVec yreactants, yproducts;
    yreactants.insertMultiple(0, 0., q.size());
    yproducts.insertMultiple(0, 0., q.size());
    // keep track of MAK monom
    map<int, int> makforward; // <int, int> --> <idSAT, power>
    map<int, int> makbackward; //
    for (auto & r: reaction->reactants)
    {
      yreactants.setUnchecked(r->idSAT, yreactants.getUnchecked(r->idSAT) + 1 );
      makforward[r->idSAT]++;
    }
    for (auto & p: reaction->products)
    {
      yproducts.setUnchecked(p->idSAT, yproducts.getUnchecked(p->idSAT) + 1 );
      makbackward[p->idSAT]++;
    }
    /*
    cout << "-- stoec vectors --" << endl;
    cout << "yreactants = ";
    for (auto & y : yreactants)
      cout << y << " ";
    cout << endl;
    cout << "yproducts = ";
    for (auto & y : yproducts)
      cout << y << " ";
    cout << endl;
    cout << "forward MAK polynom : ";
    for (auto & [key, val] : makforward)
      cout << " q_" << key << "^" << val;
    cout << endl;
    cout << "backward MAK polynom : ";
    for (auto & [key, val] : makbackward)
      cout << " q_" << key << "^" << val;
    cout << endl;
    */
    
    // forward reaction
    //cout << "-- forward reaction grad calc. --" << endl;
    double forward_prefactor = reaction->assocRate;
    double spfor = 0.;
    for (int m=0; m<p.size(); m++)
    {
      //cout << "sp check:: " << (yproducts.getUnchecked(m)-yreactants.getUnchecked(m)) << " * " << p.getUnchecked(m) << endl;
      spfor += (yproducts.getUnchecked(m)-yreactants.getUnchecked(m)) * p.getUnchecked(m);
    }
    forward_prefactor *= (exp(spfor) - 1.);
    //cout << "forward s.p = " << spfor << endl;
    //cout << "k = " << reaction->assocRate << endl;
    //cout << "forward prefac = " << forward_prefactor << endl;
    // now derivative of polynom in concentration
    // loop over all entities involved in MAK
    for (auto & [id, exponent] : makforward)
    {
      //cout << "monom = " << exponent << "*" << q.getUnchecked(id) << "^" << exponent-1;
      double monom = exponent * pow(q.getUnchecked(id), exponent-1.); // derivative of q_id
      for (auto & [id2, exponent2] : makforward) // multiply by other q_j different from q_id
      {
        if (id2==id)
          continue;
        //cout << " * " << q.getUnchecked(id2) << "^" << exponent2 << " * ";
        monom *= pow(q.getUnchecked(id2), exponent2);
      }
      //cout << endl;
      //cout << "gradH_" << id << " += " << forward_prefactor*monom << endl;
      gradqH.setUnchecked(id, gradqH.getUnchecked(id) + forward_prefactor*monom);
/*
      cout << "dH/dq current = ";
      for (auto & g : gradqH)
        cout << g << " ";
      cout << endl;
      */
    }
    
  
    
    // backward reaction
    //cout << "-- backward grad calc. --" << endl;
    double backward_prefactor = reaction->dissocRate;
    double spback = 0.;
    for (int m=0; m<p.size(); m++)
      spback += (yreactants.getUnchecked(m)-yproducts.getUnchecked(m)) * p.getUnchecked(m);
    backward_prefactor *= (exp(spback) - 1.);
    //cout << "s.p = " << spback << endl;
    //cout << "k = " << reaction->dissocRate << endl;
    //cout << "backward prefac = " << backward_prefactor << endl;
    // now derivative of polynom in concentration
    for (auto & [id, exponent] : makbackward)
    {
      //cout << "monom = " << exponent << "*" << q.getUnchecked(id) << "^" << exponent-1;
      double monom = exponent * pow(q.getUnchecked(id), exponent-1.);
      for (auto & [id2, exponent2] : makbackward)
      {
        if (id2==id)
          continue;
        //cout << " * " << q.getUnchecked(id2) << "^" << exponent2 << " * ";
        monom *= pow(q.getUnchecked(id2), exponent2);
      }
      //cout << endl;
      //cout << "gradH_" << id << " += " << backward_prefactor*monom << endl;
      gradqH.setUnchecked(id, gradqH.getUnchecked(id) + backward_prefactor*monom);
      /*
      cout << "dH/dq current = ";
      for (auto & g : gradqH)
        cout << g << " ";
      cout << endl;
      */
    }
    
  } // end reaction loop
  
  
  // creation / destruction reactions, formally treated as 0 <--> entity
  for (auto & ent : simul->entities)
  {
    //cout << "0 <--> " << ent->name << endl;
    // creation flow does not depend on q, so gradient is null
    
    // destruction flow prop to qent
    //cout << "backward" << endl;
    double destfact = ent->destructionRate * ( exp(-1.*p.getUnchecked(ent->idSAT)) - 1.);
    gradqH.setUnchecked(ent->idSAT, gradqH.getUnchecked(ent->idSAT) + destfact);
    //cout << "kd = " << ent->destructionRate << endl;
    //cout << "exp factor = " << exp(-1.*p.getUnchecked(ent->idSAT)) - 1. << endl;
    //cout << "grad coord " << ent->idSAT << " -= " << destfact << endl;
    /*
    cout << "dH/dq current = ";
    for (auto & g : gradqH)
      cout << g << " ";
    cout << endl;
     */
  }
  
  /*
  cout << "total gradient = " ;
  for (auto & g : gradqH)
    cout << g << " " ;
  cout << endl << endl;
  */
  
  for (int m=0; m<gradqH.size(); m++)
    gradqH.setUnchecked(m, gradqH.getUnchecked(m)*timescale_factor->floatValue());

  return gradqH;
  
}




void NEP::checkGradH()
{
  
  cout << "---- CHECKING dH / dq" << endl;
  
  // read init and final curve points from enum parameters
  int sstI = sst_stable->intValue();
  int sstF = sst_saddle->intValue();
  
  StateVec qI, qF;
  qI.insertMultiple(0, 0., simul->entities.size());
  qF.insertMultiple(0, 0., simul->entities.size());
  for (auto & pairI : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstI).state)
  {
    qI.set(pairI.first->idSAT, pairI.second);
  }
  for (auto & pairF : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstF).state)
  {
    qF.set(pairF.first->idSAT, pairF.second);
  }
  cout << "qI : ";
  for (auto & qi : qI)
    cout << qi <<" ";
  cout << endl;
  for (auto & qf : qF)
    cout << qf << " ";
  cout << endl;
  
  StateVec qInter;
  for (int m=0; m<qI.size(); m++)
  {
    //qInter.add( 0.5*(qI.getUnchecked(m)+qF.getUnchecked(m)));
    qInter.add(qI.getUnchecked(m));
  }
  
  cout << "qIntermediate = ";
  for (auto & q : qInter)
    cout << q << " ";
  cout << endl;
  
  StateVec ptest = {0., 0.};
  cout << "using ptest = ";
  for (auto & p : ptest)
    cout << p << " ";
  cout << endl;
  
  double epsilon = 0.001;
  cout << "epsilon = " << epsilon << endl;
  
  StateVec gradqh_anal = evalHamiltonianGradientWithQ(qInter, ptest);
  StateVec qUp_X1, qDown_X1;
  StateVec qUp_X2, qDown_X2;
  for (int m=0; m<qInter.size(); m++)
  {
    if (m==0)
    {
      qUp_X1.add(qInter.getUnchecked(m) + epsilon);
      qUp_X2.add(qInter.getUnchecked(m));
      qDown_X1.add(qInter.getUnchecked(m) - epsilon);
      qDown_X2.add(qInter.getUnchecked(m));
    }
    else
    {
      qUp_X1.add(qInter.getUnchecked(m));
      qUp_X2.add(qInter.getUnchecked(m) + epsilon);
      qDown_X1.add(qInter.getUnchecked(m));
      qDown_X2.add(qInter.getUnchecked(m) - epsilon);
    }
  }
  
  cout << "qUp_X1 = ";
  for (auto & q : qUp_X1)
    cout << q << " ";
  cout << endl;
  cout << "qDown_X1 = ";
  for (auto & q : qDown_X1)
    cout << q << " ";
  cout << endl;
  cout << "qUp_X2 = ";
  for (auto & q : qUp_X2)
    cout << q << " ";
  cout << endl;
  cout << "qDown_X2 = ";
  for (auto & q : qDown_X2)
    cout << q << " ";
  cout << endl;
  
  StateVec gradqh_num;
  gradqh_num.add( (evalHamiltonian(qUp_X1, ptest) - evalHamiltonian(qDown_X1, ptest)) / (2.*epsilon) );
  gradqh_num.add( (evalHamiltonian(qUp_X2, ptest) - evalHamiltonian(qDown_X2, ptest)) / (2.*epsilon) );
  
  
  cout << "numerical grad = ";
  for (auto & g : gradqh_num)
    cout << g << " ";
  cout << endl;
  
  cout << "analytic grad = ";
  for (auto & g : gradqh_anal)
    cout << g << " ";
  cout << endl;
  cout << endl;
  
  
}





void NEP::checkGradH2()
{
  
  cout << "---- CHECKING dH / dp" << endl;
  
  // read init and final curve points from enum parameters
  int sstI = sst_stable->intValue();
  int sstF = sst_saddle->intValue();
  
  StateVec qI, qF;
  qI.insertMultiple(0, 0., simul->entities.size());
  qF.insertMultiple(0, 0., simul->entities.size());
  for (auto & pairI : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstI).state)
  {
    qI.set(pairI.first->idSAT, pairI.second);
  }
  for (auto & pairF : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstF).state)
  {
    qF.set(pairF.first->idSAT, pairF.second);
  }
  
  StateVec qInter;
  for (int m=0; m<qI.size(); m++)
  {
    //qInter.add( 0.5*(qI.getUnchecked(m)+qF.getUnchecked(m)));
    qInter.add(qI.getUnchecked(m));
  }
  
  cout << "qIntermediate = ";
  for (auto & q : qInter)
    cout << q << " ";
  cout << endl;
  
  StateVec ptest = {0., 0.};
  cout << "using ptest = ";
  for (auto & p : ptest)
    cout << p << " ";
  cout << endl;
  
  double epsilon = 0.001;
  cout << "epsilon = " << epsilon << endl;
  
  StateVec gradph_anal = evalHamiltonianGradientWithP(qInter, ptest);
  StateVec pUp_X1, pDown_X1;
  StateVec pUp_X2, pDown_X2;
  for (int m=0; m<ptest.size(); m++)
  {
    if (m==0)
    {
      pUp_X1.add(ptest.getUnchecked(m) + epsilon);
      pUp_X2.add(ptest.getUnchecked(m));
      pDown_X1.add(ptest.getUnchecked(m) - epsilon);
      pDown_X2.add(ptest.getUnchecked(m));
    }
    else
    {
      pUp_X1.add(ptest.getUnchecked(m));
      pUp_X2.add(ptest.getUnchecked(m) + epsilon);
      pDown_X1.add(ptest.getUnchecked(m));
      pDown_X2.add(ptest.getUnchecked(m) - epsilon);
    }
  }
  
  cout << "pUp_X1 = ";
  for (auto & p : pUp_X1)
    cout << p << " ";
  cout << endl;
  cout << "pDown_X1 = ";
  for (auto & p : pDown_X1)
    cout << p << " ";
  cout << endl;
  cout << "pUp_X2 = ";
  for (auto & p : pUp_X2)
    cout << p << " ";
  cout << endl;
  cout << "pDown_X2 = ";
  for (auto & p : pDown_X2)
    cout << p << " ";
  cout << endl;
  
  StateVec gradph_num;
  gradph_num.add( (evalHamiltonian(qInter, pUp_X1) - evalHamiltonian(qInter, pDown_X1)) / (2.*epsilon) );
  gradph_num.add( (evalHamiltonian(qInter, pUp_X2) - evalHamiltonian(qInter, pDown_X2)) / (2.*epsilon) );
  
  
  cout << "numerical grad = ";
  for (auto & g : gradph_num)
    cout << g << " ";
  cout << endl;
  
  cout << "analytic grad = ";
  for (auto & g : gradph_anal)
    cout << g << " ";
  cout << endl;
  cout << endl;
  
  
}



void NEP::reset()
{
  // reset previous calculations
  actionDescent.clear();
  trajDescent.clear();
  dAdqDescent.clear();
  dAdqDescent_filt.clear();
  g_qcurve.clear();
  g_pcurve.clear();
  g_times.clear();
  dAdq.clear();
  dAdq_filt.clear();
  ham_descent.clear();
  action = 10.;
  length_qcurve = 0.;
  stepDescent = stepDescentInitVal->floatValue();
  cutoffFreq->setValue(0.05);
}


void NEP::stop()
{
  state = Idle;
  cout << "[DEBUG] stop() NEP state = " << toString(state) << endl;
}



// start thread
void NEP::run()
{
  //cout << "nepnotifier size = " << nepNotifier.size() << endl;
  
  simul->affectSATIds();
  reset();
  
  /*
  //for debugging gradient calculations
  checkGradH();
  checkGradH2();
  return;
  */
  /*
   //for debugging the filtering step
  debugFiltering();
   return;
   */
  
  // has bad behavior for now, trajectory eventually diverges
  // need deeper understanding
  // see https://web.pa.msu.edu/people/dykman/pub06/jcp100_5735.pdf
  if (heteroclinic_study)
  {
    heteroclinicStudy();
    heteroclinic_study = false;
    return;
  }

  
  if (maxPrinting->boolValue())
  {
    system("mkdir -p debug");
    debugfile.open("./debug/DEBUG.txt", ofstream::out | ofstream::trunc);
    debugfile << "\t\t\t------ DEBUG ------" << endl;
    debugfile << "Descent parameters" << endl;
    debugfile << "sampling points : " << nPoints->intValue() << endl;
  }
  
  // init concentration curve
  cout << "init g_qcurve" << endl;
  //initConcentrationCurve();
  testinitConcentrationCurve();
  
  int count = 0;
  //nepNotifier.addMessage(new NEPEvent(NEPEvent::WILL_START, this)); // #silent
  //while (count < Niterations->intValue() && !threadShouldExit())
  //cout << descentShouldContinue(count+1) << " && " << !threadShouldExit() << endl;
  while (descentShouldContinue(count+1) && !threadShouldExit())
  {
    
    count++;
    if (count==1)
      cout << "initial value of action = " << action << endl;
    cout << "\niteration #" << count << endl;
    
    if (count>1)
    {
      //stepDescent = backTrackingMethodForStepSize(g_qcurve, dAdq_filt);
      stepDescent = backTrackingMethodForStepSize(g_qcurve);
      cout << "using step = " << stepDescent << endl;
      updateOptimalConcentrationCurve(g_qcurve, stepDescent);
    }
    
    if (maxPrinting->boolValue())
    {
      debugfile << "\nIteration " << count << endl;
      debugfile << "-- concentration curve --" << endl;
      for (int p=0; p<nPoints->intValue(); p++)
      {
        debugfile << "(";
        int c=0;
        for (auto & qm : g_qcurve.getUnchecked(p))
        {
          string comma = (c == g_qcurve.getUnchecked(p).size()-1 ? ") " : ",");
          debugfile << qm << comma ;
          c++;
        }
      }
      debugfile << endl;
    }
    
    // lift current trajectory to full (q ; p; t) space
    // this function updates global variables g_pcurve and times
    cout << "lifting trajectory" << endl;
    //LiftTrajectoryOptResults liftoptres = liftCurveToTrajectoryWithNLOPT();
    LiftTrajectoryOptResults liftoptres = liftCurveToTrajectoryWithGSL(g_qcurve);
    cout << "end lifting" << endl;
    
    // update global variable with lift results
    g_pcurve = liftoptres.pcurve;
    g_times = liftoptres.times;
    
    // keep track of trajectory update in (q ; p) space
    Trajectory newtraj;
    Array<double> hams;
    for (int point=0; point<nPoints->intValue(); point++)
    {
      PhaseSpaceVec psv;
      for (auto & qm : g_qcurve.getUnchecked(point))
        psv.add(qm);
      for (auto & pm : g_pcurve.getUnchecked(point))
        psv.add(pm);
      newtraj.add(psv);
      hams.add(evalHamiltonian(g_qcurve.getUnchecked(point), g_pcurve.getUnchecked(point))); 
    }
    //cout << "adding a trajectory of size : " << newtraj.size() << " = " << g_qcurve.size() << " + " << g_pcurve.size() << endl;
    trajDescent.add(newtraj);
    ham_descent.add(hams);
    
    if (maxPrinting->boolValue())
    {
      debugfile << "-- momentum curve --" << endl;
      for (int p=0; p<nPoints->intValue(); p++)
      {
        debugfile << "(";
        int c=0;
        for (auto & pm : g_pcurve.getUnchecked(p))
        {
          string comma = (c == g_pcurve.getUnchecked(p).size()-1 ? ") " : ",");
          debugfile << pm << comma ;
          c++;
        }
      }
      debugfile << endl;
      debugfile << "-- time sampling --" << endl;
      //cout << "times.size = " << g_times.size() << endl;
      for (int p=0; p<nPoints->intValue(); p++)
      {
        debugfile << g_times.getUnchecked(p) << " " ;
      }
      debugfile << endl;
    }
  
    
    // calculate action value
    cout << "calculating action" << endl;
    double newaction = calculateAction(g_qcurve, g_pcurve, g_times);
    double diffAction = abs(action - newaction);
    //actionDescent.add(diffAction);
    actionDescent.add(newaction);
    
    if (maxPrinting->boolValue())
    {
      debugfile << "-- Action --" << endl;
      debugfile << "S = " << newaction << " & deltaS = " << diffAction << endl;
    }
    
    // message to async to monitor the descent
    cout << "in NEP : " << newaction << ". abs diff = " << diffAction << endl;
    //nepNotifier.addMessage(new NEPEvent(NEPEvent::NEWSTEP, this, count, newaction, cutoffFreq->floatValue(), nPoints->intValue(), metric)); // #silent
    
    
    // check algorithm descent status
    bool shouldUpdate = descentShouldUpdateParams(diffAction);
    if (shouldUpdate && count>1)
    {
      cout << "descentShouldUpdateParams() returned true" << endl;
      updateDescentParams();
      cout << "resampling in time uniform" << endl;
      //resampleInTimeUniform(g_qcurve, g_qcurve.size());
      cout << "filtering in time uniform" << endl;
      //lowPassFiltering(g_qcurve, true);
      cout << "Resample in space uniform" << endl;
      //resampleInSpaceUniform(g_qcurve, g_qcurve.size());
      cout << "lift to (q, p, t)" << endl;
      //liftCurveToTrajectoryWithGSL();
      cout << "done" << endl;
      // increase sampling of concentration curve is optionnal. Not implemented at the moment.
      //continue; // next iteration using the filtered g_qcurve
    }
    
    
    // dA / dq
    cout << "--- dAdq printing ---" <<endl;
    // Array<StateVec> dAdq;
    for (int point=0; point<nPoints->intValue(); point++)
    {
      StateVec dHdqk = evalHamiltonianGradientWithQ(g_qcurve.getUnchecked(point), g_pcurve.getUnchecked(point));
      StateVec dpdtk;
      dpdtk.insertMultiple(0, 0., nPoints->intValue());
      if (point>0 && point<(nPoints->intValue()-1))
      {
        for (int m=0; m<dHdqk.size(); m++)
        {
          double dpm = liftoptres.opt_momentum.getUnchecked(point).getUnchecked(m) - liftoptres.opt_momentum.getUnchecked(point-1.).getUnchecked(m);
          double dtm = 0.5*(liftoptres.opt_deltaT.getUnchecked(point) + liftoptres.opt_deltaT.getUnchecked(point-1));
          dpdtk.setUnchecked(m, dpm/dtm);
        }
      }
      //cout << "point " << point << endl;
      StateVec dAdqk;
      for (int m=0; m<dHdqk.size(); m++)
      {
        dAdqk.add(-dHdqk.getUnchecked(m) - dpdtk.getUnchecked(m));
        //cout << "\t" << -dHdqk.getUnchecked(m) << " " << - dpdtk.getUnchecked(m) << endl;
      }
      
      dAdq.add(dAdqk);
    }
    dAdqDescent.add(dAdq);
    
    // filter gradient
    dAdq_filt = dAdq;
    lowPassFiltering(dAdq_filt, false);
    dAdqDescent_filt.add(dAdq_filt);
   
    if (maxPrinting->boolValue())
    {
      debugfile << "-- dAdq --" << endl;
      for (int p=0; p<nPoints->intValue(); p++)
      {
        debugfile << "(";
        StateVec dAdqk = dAdq.getUnchecked(p);
        int c=0;
        for (auto & coord : dAdqk)
        {
          string comma = ( c==dAdqk.size()-1 ? ")" : "," );
          debugfile << coord << comma;
          c++;
        }
      }
      debugfile << endl;
    }
    
    
    action = newaction;
    // keep track of action history
    cout << "action = " << action << endl;
    
    //cout << "updating concentration curve" << endl;
    // now update the concentration trajectory with functionnal gradient descent
    // this function update global variable g_qcurve
    //updateOptimalConcentrationCurve_old(liftoptres.opt_momentum, liftoptres.opt_deltaT);
        
    
  } // end while
  
  cout << actionDescent.size() << " --- " << trajDescent.size() << endl;
  
  // save descent algorithm results into a file
  cout << "writing to file" << endl;
  writeDescentToFile();
  
  stop();
  
  
}


// #TODO
// Split this method into several :
// 1/ GSL implementation that returns p_star and dt
// 2/ lift operation, i.e. build p from q and p_star
// 3/ Moving average on newly built p to reduce noise in p solving
LiftTrajectoryOptResults NEP::liftCurveToTrajectoryWithGSL(Curve& qcurve)
{
  //cout << "--- NEP::liftCurveToTrajectoryWithGSL() ---" << endl;
  // dimension of the problem
  const int n = simul->entities.size() + 1; // number of entities + 1 (time)
  
  Array<double> vec_dt; // vector of optimal time assigned between each q(i) and q(i+1)
  Array<StateVec> vec_pstar; // vector of optimal momenta assigned between each q(i) and q(i+1)
  
  // loop over points in concentration space
  // q : q0 -- p0 -- q1 -- p1 --  .. -- qi -- pi -- q(i+1) -- pi -- ... qn(-1) -- p(n-1) -- qn
  for (int k=0; k<nPoints->intValue()-1; k++) // n - 1 iterations
  {
    //cout << "qcurve point #" << k << endl;
    
    // calculate q, dq of current concentration curve
    StateVec q = qcurve.getUnchecked(k);
    StateVec qnext = qcurve.getUnchecked(k+1);
    jassert(q.size() == qnext.size());
    StateVec qcenter;
    Array<double> deltaq;
    for (int m=0; m<q.size(); m++)
    {
      deltaq.add(qnext.getUnchecked(m) - q.getUnchecked(m));
      qcenter.add( 0.5* (q.getUnchecked(m) + qnext.getUnchecked(m)));
    }
    
    
    
    // encaps useful variables to pass to GSL
    EncapsVarForGSL ev;
    ev.qcenter = &qcenter;
    ev.deltaq = &deltaq;
    ev.nep = this;
    ev.scale = 1.;
    
    
    // function to solve
    //gsl_multiroot_function f0;
    //f0.f = residual4GSL;
    //f0.n = n;
    //f0.params = &ev;
    
    // initial value for p and dt
    // p
    gsl_vector* x = gsl_vector_alloc(n);
    StateVec pinit;
    for (int m=0; m<n-1; m++)
    {
      double pm = 0.1;
      gsl_vector_set(x, m, pm);
      pinit.add(pm);
    }
    // dt = (dq•dH/dp) / || dH/dp ||^2
    StateVec dHdp = evalHamiltonianGradientWithP(qcenter, pinit);
    double norm2 = 0.;
    double sp = 0.;
    for (int m=0; m<pinit.size(); m++)
    {
      norm2 += dHdp.getUnchecked(m)*dHdp.getUnchecked(m);
      sp += qcenter.getUnchecked(m)*dHdp.getUnchecked(m);
    }
    norm2 = sqrt(norm2);
    double dtinit = 1.;
    if (norm2>0.)
      dtinit = abs(sp) / norm2;
    else
    {
      //LOGWARNING("|| dH/dp || = 0, dt initialized to 1");
      //cout << "dH/dp = ";
      //for (int k=0; k<dHdp.size(); k++)
      //  cout << dHdp.getUnchecked(k) << " ";
      //cout << endl;
    }
    gsl_vector_set(x, n-1, dtinit);
    
    /*
    // init the solver to solve for dt at p held fixed
    const gsl_multiroot_fsolver_type * T0 = gsl_multiroot_fsolver_hybrids;
    gsl_multiroot_fsolver * s0 = gsl_multiroot_fsolver_alloc(T0, 1);
    gsl_multiroot_fsolver_set(s0, &f, x);
    */
    
    //gslSolve();
    
    
    gsl_multiroot_function_fdf fdf; // using jacobian
    fdf.f = residual4GSL;
    fdf.df = residual4GSL_df;
    fdf.fdf = residual4GSL_fdf; // combines function to evaluate and the jacobian
    fdf.n = n;
    fdf.params = &ev;
    
    // init gsl solver withtout derivative
    const gsl_multiroot_fdfsolver_type * T = gsl_multiroot_fdfsolver_hybridj;
    gsl_multiroot_fdfsolver * s = gsl_multiroot_fdfsolver_alloc(T, n);
    gsl_multiroot_fdfsolver_set(s, &fdf, x);
    
    
        
    // iterate to solve
    // set scale of the system
    double epsilon = 0.;
    int status = GSL_CONTINUE;
    int iter = 0;
    int maxiter = 20;
    double tolerance = 1e-10;
    
    for (int e=0; e<10; e++)
    {
      ev.scale = epsilon;
      fdf.params = &ev;
      iter = 0;
      status = GSL_CONTINUE;
      //cout << "\tepsilon = " << epsilon << endl;
      
      // set initial guess to output of previous iteration
      gsl_vector * xprev = s->x;
      gsl_multiroot_fdfsolver_set(s, &fdf, xprev);
      
      while (status == GSL_CONTINUE && iter <= maxiter)
      {
        iter++;
        //cout << "\titer" << iter << endl;
        //status = gsl_multiroot_fsolver_iterate(s); // if I'm using the jacobian gsl_multiroot_fdfsolver_iterate
        status = gsl_multiroot_fdfsolver_iterate(s);
        if (status)
          break;
        status = gsl_multiroot_test_residual(s->f, tolerance);
        double norm2 = 0.;
        for (int k=0; k<s->f->size; k++)
          norm2 += gsl_vector_get(s->f, k)*gsl_vector_get(s->f, k);
        norm2 = sqrt(norm2);
        //cout << "\tresidual : " << norm2 << endl;
      }
      //std::cout << "\tstatus = " << gsl_strerror(status) << "\n";
      epsilon += 1./10.;
    }
    
    // some printing
    //std::cout << "FINAL status = " << gsl_strerror(status) << "\n";
    
  

    //std::cout << "p0 = " << gsl_vector_get(s->x, 0) << "\n";
    //std::cout << "p1 = " << gsl_vector_get(s->x, 1) << "\n";
    //std::cout << "dt = " << gsl_vector_get(s->x, 1) << "\n";
    //cout << "used " << iter << " iterations" << endl;
    
    // retrieve results in a non-GSL form
    StateVec pstar;
    for (int m=0; m<n-1; m++)
      pstar.add(gsl_vector_get(s->x, m));
    //double dt = gsl_vector_get(s->x, n-1);
    double tau = gsl_vector_get(s->x, n-1);
    double dt = exp(tau);
    
    /*
    double Hscale = evalHamiltonian(qcenter, pstar);
    StateVec dHdpscale = evalHamiltonianGradientWithP(qcenter, pstar);
    dsp::Matrix<double> hessian = evalHamiltonianHessianWithP(qcenter, pstar);
    
    cout << "-- Scaling of the problem --" << endl;
    cout << "f0 = " << Hscale << endl;
    for (int k=0; k<dHdpscale.size(); k++)
    {
      cout << "f" << k+1 << " = " << dHdpscale.getUnchecked(k)*dt - deltaq.getUnchecked(k) << endl;
    }
    
    
    cout << "J = ";
    for (int i=0; i<n; i++)
    {
      for (int j=0; j<n; j++)
      {
        if (i==0 && j<n-1)
          cout << dHdpscale.getUnchecked(j) << " ";
        else if (i==0 && j==n-1)
          cout << "0";
        else if (i>0 && j<n-1)
          cout << hessian(i-1, j) << " ";
        else if (i>0 && j==n-1)
          cout << dHdpscale.getUnchecked(i-1);
      }
      cout << endl;
    }
     */
    
    // add optimizing time
    //opt_deltaT.add(ev->t_opt);
    vec_dt.add(dt);
    
    // add optimizing momentum vector
    vec_pstar.add(pstar);
    
    //gsl_multiroot_fsolver_free(s);
    gsl_multiroot_fdfsolver_free(s);
    gsl_vector_free(x);
    
  } // end loop over points in concentration curve
  

  // Build full trajectory in (q ; p) space from optima found previously
  //pcurve.clear();
  //times.clear();
  pCurve pcurve;
  Array<double> times;
  
  // init a null vector
  Array<double> nullP;
  for (int i=0; i<Simulation::getInstance()->entities.size(); i++)
    nullP.add(0.);

  // first elements are 0
  double sumtime = 0.;
  pcurve.add(nullP);
  times.add(sumtime);
  for (int k=1; k<nPoints->intValue(); k++) // nPoints-1 iterations
  {
    if (k==0)
      continue;
        
    // handle time
    sumtime += vec_dt.getUnchecked(k-1);
    times.add(sumtime);
    
    // handle momentum, mean between current and next p
    if (k==nPoints->intValue()-1) // force last momentum vec to be 0
      pcurve.add(nullP);
    else
    {
      StateVec meanP;
      for (int m=0; m<vec_pstar.getUnchecked(k).size(); m++)
      {
        double pm = 0.5*(vec_pstar.getUnchecked(k-1).getUnchecked(m) + vec_pstar.getUnchecked(k).getUnchecked(m));
        meanP.add(pm);
      }
      pcurve.add(meanP);
    }
  }

  jassert(pcurve.size() == qcurve.size());
  jassert(times.size() == qcurve.size());
  
  // moving average on pcurve (execpt first and last point that must remain 0)
  int window = 3;
  Trajectory av_pcurve;
  for (int k=0; k<pcurve.size(); k++)
  {
    StateVec avp;
    // loop over dimensions
    for (int dim=0; dim<pcurve.getUnchecked(k).size(); dim++)
    {
      int w = min(min(window, k), pcurve.size()-1-k);
      double av = 0.;
      double c = 0.;
      for (int k2=k-w; k2<=k+w; k2++)
      {
        c++;
        av += pcurve.getUnchecked(k2).getUnchecked(dim);
      }
      av /= c;
      avp.add(av);
    }
    jassert(avp.size() == n-1);
    av_pcurve.add(avp);
  }
  
  jassert(av_pcurve.size() == pcurve.size());
  //cout << "average pcurve size : " << av_pcurve.size() << endl;
  
  // for debugging
  if (maxPrinting->boolValue())
  {
    debugfile << "-- lifting optima found --" << endl;
    debugfile << "p* = ";
    for (auto & ppoint : vec_pstar)
    {
      debugfile << "(";
      int c=0;
      for (auto & pm : ppoint)
      {
        string comma = ( c==ppoint.size()-1 ? ") " : "," );
        debugfile << pm << comma;
        c++;
      }
    }
  debugfile << endl;
  debugfile << "dt = ";
  for (auto & tpoint : vec_dt)
  {
    debugfile << tpoint << " ";
  }
  debugfile << endl;
  }
  /*
  // update global variables or not
  if (updateGlobalVar)
  {
    g_pcurve = pcurve;
    g_times = times;
  }
  */
  
  // Return optimization results
  LiftTrajectoryOptResults output;
  output.opt_deltaT = vec_dt;
  output.opt_momentum = vec_pstar;
  output.pcurve = pcurve;
  output.times = times;
  
  
  
  return output;
  
}




/*
LiftTrajectoryOptResults NEP::liftCurveToTrajectoryWithNLOPT_old()
{
  int nent = Simulation::getInstance()->entities.size();
  //nlopt::opt opt(nlopt::LD_LBFGS, nent);  // momentum is nentities dimensionnal
  nlopt::opt opt(nlopt::LN_COBYLA, nent);  // momentum is nentities dimensionnal
  //nlopt::opt opt(nlopt::LD_MMA, nent);
  

  // lower and upper bound for optimization
  vector<double> lowerbound_p(nent, -50.0); // #para
  vector<double> upperboundb_p(nent, 50.0);
  opt.set_lower_bounds(lowerbound_p);
  opt.set_upper_bounds(upperboundb_p);
  opt.set_maxeval(1000);    // nombre d’itérations max
  
  
  Array<double> opt_deltaT; // vector of optimal time assigned between each q(i) and q(i+1)
  Array<StateVec> opt_momentum; // vector of optimal momenta assigned between each q(i) and q(i+1)
  
  
  // assign first points along curve
  //opt_deltaT.add(0.);
  Array<double> nullP, dummyP;
  for (int i=0; i<Simulation::getInstance()->entities.size(); i++)
  {
    nullP.add(0.);
    dummyP.add(0.);
  }
  //opt_momentum.add(nullP);
  
  // loop over points in concentration space
  
  // q : q0 -- p0 -- q1 -- p1 --  .. -- qi -- pi -- q(i+1) -- pi -- ... qn(-1) -- p(n-1) -- qn
  //for (int k=0; k<qcurve.size()-1; k++) // n - 1 iterations
  for (int k=0; k<nPoints->intValue()-1; k++) // n - 1 iterations
  {
    //cout << "optimizing point #" << k << endl;
    StateVec q = g_qcurve.getUnchecked(k);
    StateVec qnext = g_qcurve.getUnchecked(k+1);
    jassert(q.size() == qnext.size());
    StateVec qcenter;
    Array<double> deltaq;
    for (int i=0; i<q.size(); i++)
    {
      deltaq.add(qnext.getUnchecked(i) - q.getUnchecked(i));
      qcenter.add( 0.5* (q.getUnchecked(i) + qnext.getUnchecked(i)));
    }
    
    // set maximization objective with respect to p variable
    EncapsVarForNLOpt * ev = new EncapsVarForNLOpt{&qcenter, &deltaq,  &dummyP, this};
    
    //opt.set_max_objective(objective_max_p, (void*)& deltaq);
    opt.set_max_objective(objective_max_p, (void*) ev);
    opt.set_xtol_rel(1e-5);
    
    // add constraint to optimization
    opt.add_equality_constraint(constraint_hamiltonian, (void*) ev, 1e-10);
    
    std::vector<double> p_opt(q.size(), 0.0); // init popt with null vector
    double maxH;
    
    //cout << "will start optimization" << endl;
    
    // start optimization
    //nlopt::result result = opt.optimize(p_opt, maxH);
    try
    {
      //nlopt::result result = opt.optimize(p_opt, maxH);
      opt.optimize(p_opt, maxH);
      //std::cout << "Optimization success, result = " << result << std::endl;
    } catch (std::exception &e)
    {
      LOGWARNING("NLopt crashed with error message : " <<  e.what());
    }
    
    // better resolution of the search
    
    
    // assign time interval deduced from optimisation in p
    StateVec parr_opt;
    for (auto & pi : p_opt)
      parr_opt.add(pi);
    StateVec gradpH = evalHamiltonianGradientWithP(qcenter, parr_opt);
    double norm2 = 0.;
    double deltaT = 0.;
    for (int i=0; i<gradpH.size(); i++)
    {
      norm2 += gradpH.getUnchecked(i) * gradpH.getUnchecked(i);
      deltaT += gradpH.getUnchecked(i) * deltaq.getUnchecked(i);
    }
    if (norm2>0.)
      deltaT /= norm2;
    else
    {
      LOGWARNING("gradient of hamiltonian in p has null norm, take results with caution.");
    }
    
    
    cout << "--- delta T calculation ---" << endl;
    cout << "deltaq = ";
    for (auto & dq : deltaq)
      cout << dq << " ";
    cout << endl;
    cout << "dH/dp = ";
    for (auto & gp : gradpH)
      cout << gp << " ";
    cout << endl;
    cout << "deltaT = " << deltaT << endl;
    
    
    cout << "--- optima found ---" << endl;
    cout << "qcenter = ";
    for (auto & qc : qcenter)
      cout << qc << " ";
    cout << endl;
    cout << "deltaT = " << deltaT << endl;
    cout << "p = ";
    for (auto & pi : p_opt)
      cout << pi << " ";
    cout << endl;
    cout << "--- ---" << endl;
    
    
    // add optimizing time
    //opt_deltaT.add(ev->t_opt);
    opt_deltaT.add(deltaT);
    
    // add optimizing momentum vector
    opt_momentum.add(parr_opt);
    
    //cout << "Optimal t = " << ev.t_opt << endl;
    
    //std::cout << "Optimal F(p, t*) = " << -maxf << std::endl;
  } // end loop over current trajectory
  
  //cout << "finished optimizing" << endl;
  
  jassert(opt_deltaT.size() == opt_momentum.size());
  jassert(opt_deltaT.size() == nPoints->intValue()-1);
  
  // Build full trajectory in (q ; p) space from optima found previously
  //Array<double> tTraj;
  //Curve pTraj;
  g_pcurve.clear();
  g_times.clear();
  

  // first elements are 0
  double sumtime = 0.;
  g_pcurve.add(nullP);
  g_times.add(sumtime);
  for (int k=1; k<nPoints->intValue(); k++) // nPoints-1 iterations
  {
    if (k==0)
      continue;
    
    //cout << "k = " << k << endl;
    
    // handle time
    sumtime += opt_deltaT.getUnchecked(k-1);
    g_times.add(sumtime);
    
    // handle momentum, mean between current and next p
    if (k==nPoints->intValue()-1) // force last momentum vec to be 0
      g_pcurve.add(nullP);
    else
    {
      StateVec meanP;
      for (int m=0; m<opt_momentum.getUnchecked(k).size(); m++)
      {
        double pm = 0.5*(opt_momentum.getUnchecked(k-1).getUnchecked(m) + opt_momentum.getUnchecked(k).getUnchecked(m));
        meanP.add(pm);
      }
      g_pcurve.add(meanP);
    }
  }
  
  
  // TODO
  // smooth g_pcurve
  
  
  cout << "--- popt ---" << endl;
  for (auto & ppoint : opt_momentum)
  {
    for (auto & pm : ppoint)
      cout << pm << " ";
    cout << endl;
  }
  cout << "--- deltaT opt ---" << endl;
  for (auto & t : opt_deltaT)
    cout << t << " ";
  cout << endl;
  

  cout << "--- g_pcurve ---" << endl;
  for (auto & ppoint : g_pcurve)
  {
    for (auto & pm : ppoint)
      cout << pm << " ";
    cout << endl;
  }
  cout << "--- times ---" << endl;
  for (auto & t : times)
    cout << t << " ";
  cout << endl;
  
  cout << "----------- END lift curve ----------" << endl;


  jassert(g_pcurve.size() == g_qcurve.size());
  jassert(g_times.size() == g_qcurve.size());
  
  
  // Return optimization results
  LiftTrajectoryOptResults output;
  output.opt_deltaT = opt_deltaT;
  output.opt_momentum = opt_momentum;
  
  if (maxPrinting->boolValue())
  {
    debugfile << "-- lifting optima found --" << endl;
    debugfile << "p* = ";
    for (auto & ppoint : opt_momentum)
    {
      debugfile << "(";
      int c=0;
      for (auto & pm : ppoint)
      {
        string comma = ( c==ppoint.size()-1 ? ") " : "," );
        debugfile << pm << comma;
        c++;
      }
    }
  debugfile << endl;
  debugfile << "deltaT = ";
  for (auto & tpoint : opt_deltaT)
  {
    debugfile << tpoint << " ";
  }
  debugfile << endl;
  }
  
  return output;
  
}


*/

void NEP::testinitConcentrationCurve()
{
  g_qcurve.clear();
  g_qcurve.add({ 2.165380239 , 1.092999816 });
  g_qcurve.add({ 2.17939 , 1.09388 });
  g_qcurve.add({ 2.19303 , 1.09474 });
  g_qcurve.add({ 2.20698 , 1.09563 });
  g_qcurve.add({ 2.22067 , 1.09651 });
  g_qcurve.add({ 2.23442 , 1.09739 });
  g_qcurve.add({ 2.24828 , 1.09829 });
  g_qcurve.add({ 2.26186 , 1.09918 });
  g_qcurve.add({ 2.27587 , 1.10011 });
  g_qcurve.add({ 2.2899 , 1.10104 });
  g_qcurve.add({ 2.30355 , 1.10196 });
  g_qcurve.add({ 2.31741 , 1.1029 });
  g_qcurve.add({ 2.33128 , 1.10385 });
  g_qcurve.add({ 2.34497 , 1.1048 });
  g_qcurve.add({ 2.35826 , 1.10573 });
  g_qcurve.add({ 2.37227 , 1.10673 });
  g_qcurve.add({ 2.38561 , 1.10768 });
  g_qcurve.add({ 2.39952 , 1.10869 });
  g_qcurve.add({ 2.41397 , 1.10976 });
  g_qcurve.add({ 2.42742 , 1.11076 });
  g_qcurve.add({ 2.44125 , 1.11181 });
  g_qcurve.add({ 2.45543 , 1.1129 });
  g_qcurve.add({ 2.4683 , 1.1139 });
  g_qcurve.add({ 2.48303 , 1.11507 });
  g_qcurve.add({ 2.49631 , 1.11615 });
  g_qcurve.add({ 2.50973 , 1.11725 });
  g_qcurve.add({ 2.52324 , 1.11838 });
  g_qcurve.add({ 2.53679 , 1.11954 });
  g_qcurve.add({ 2.55034 , 1.12073 });
  g_qcurve.add({ 2.56554 , 1.12208 });
  g_qcurve.add({ 2.57894 , 1.12331 });
  g_qcurve.add({ 2.59219 , 1.12455 });
  g_qcurve.add({ 2.60524 , 1.12581 });
  g_qcurve.add({ 2.61965 , 1.12724 });
  g_qcurve.add({ 2.63368 , 1.12867 });
  g_qcurve.add({ 2.6473 , 1.13011 });
  g_qcurve.add({ 2.66045 , 1.13154 });
  g_qcurve.add({ 2.67446 , 1.13312 });
  g_qcurve.add({ 2.68779 , 1.13469 });
  g_qcurve.add({ 2.70164 , 1.13639 });
  g_qcurve.add({ 2.71572 , 1.1382 });
  g_qcurve.add({ 2.72975 , 1.14011 });
  g_qcurve.add({ 2.74252 , 1.14194 });
  g_qcurve.add({ 2.75654 , 1.14409 });
  g_qcurve.add({ 2.77021 , 1.14634 });
  g_qcurve.add({ 2.78358 , 1.14875 });
  g_qcurve.add({ 2.79721 , 1.15147 });
  g_qcurve.add({ 2.81067 , 1.15454 });
  g_qcurve.add({ 2.8241 , 1.15824 });
  g_qcurve.add({ 2.836659908 , 1.163339972 });

  cout << "qcurve size = " << g_qcurve.size() << endl;
  nPoints->setValue(g_qcurve.size());

  
}



void NEP::initConcentrationCurve()
{
  // read init and final curve points from enum parameters
  int sstI = sst_stable->intValue();
  int sstF = sst_saddle->intValue();
  
  StateVec qI, qF;
  qI.insertMultiple(0, 0., simul->entities.size());
  qF.insertMultiple(0, 0., simul->entities.size());
  for (auto & pairI : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstI).state)
  {
    qI.set(pairI.first->idSAT, pairI.second);
  }
  for (auto & pairF : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstF).state)
  {
    qF.set(pairF.first->idSAT, pairF.second);
  }
  /*
  cout << "qI : ";
  for (auto & qi : qI)
    cout << qi <<" ";
  cout << endl;
  for (auto & qf : qF)
    cout << qf << " ";
  cout << endl;
  */
  
  jassert(qI.size() == simul->entities.size());
  jassert(qF.size() == simul->entities.size());
  
  // init with straight line between qI and qF
  g_qcurve.clear();
  double NN = (double) nPoints->intValue();
  jassert(nPoints->intValue()>1);
  for (int point=0; point<nPoints->intValue(); point++)
  {
    StateVec vec;
    double fpoint = (double) point;
    for (int k=0; k<qI.size(); k++)
    {
      double qk = qF.getUnchecked(k) + (1. - fpoint/(NN-1.)) * (qI.getUnchecked(k) - qF.getUnchecked(k));
      vec.add(qk);
    }
    g_qcurve.add(vec);
  }
  
  // init sample rate
  length_qcurve = curveLength(g_qcurve);
  if (length_qcurve>0.)
    sampleRate = (double) nPoints->intValue() / length_qcurve;
  else
  {
    LOGWARNING("qcurve has null length !!");
    sampleRate = 1000.;
  }
  /*
  // debugging
  cout << "curve size after init : " << g_qcurve.size() << ". nPoints = " << nPoints->intValue() << endl;
  cout << "points are : " << endl;
  int c=-1;
  for (auto & q : g_qcurve)
  {
    c++;
    cout << "point #" << c << "   : ";
    for (auto & qi : q)
      cout << qi << " ";
    cout << endl;
  }
  */
  
}

void NEP::filterConcentrationTrajectory() // old
{
  cout << "filtering concentration curve" << endl;
  // filter the gradient
  //filter.setCutoffFrequency(cutoffFreq->floatValue());
  //filter.prepare(sampleRate, simul->entities.size());
  //filter.setSamplingRate(sampleRate);
  //filter.setCutoffFrequency(cutoffFreq->floatValue());
  //filter.process(g_qcurve);
}


void NEP::updateDescentParams()
{
  cout << "updating descent params" << endl;
  cutoffFreq->setValue(cutoffFreq->floatValue() + 0.01);
  stepDescent = stepDescentInitVal->floatValue();
}


bool NEP::descentShouldUpdateParams(double diffAction)
{
  if ((diffAction<action_threshold->floatValue() || stepDescent<stepDescentThreshold))
  {
    bool b1 = diffAction<action_threshold->floatValue();
    bool b2 = stepDescent<stepDescentThreshold;
    //cout << "Will update descent params. action criteria : " << b1;
    //cout << ". step descent criteria : " << b2 << endl;
  }
  return ((diffAction<action_threshold->floatValue() || stepDescent<stepDescentThreshold));
}

bool NEP::descentShouldContinue(int step)
{
  bool b = step<=Niterations->intValue();
  bool b2 = cutoffFreq->floatValue()<maxcutoffFreq->floatValue();
  return (step<=Niterations->intValue() && cutoffFreq->floatValue()<maxcutoffFreq->floatValue());
}


void NEP::writeDescentToFile()
{
  // open output file
  String filename = "action-functionnal-descent.csv";
  ofstream historyFile;
  historyFile.open(filename.toStdString(), ofstream::out | ofstream::trunc);
  
  historyFile << "iteration,action,point";
  for (auto & ent : simul->entities)
    historyFile << ",q_" << ent->name;
  for (auto & ent : simul->entities)
    historyFile << ",p_" << ent->name;
  for (auto & ent : simul->entities)
    historyFile << ",dAdq_" << ent->name;
  for (auto & ent : simul->entities)
    historyFile << ",dAdq_filt_" << ent->name;
  historyFile << ",H";
  historyFile << endl;
  cout << "action descent size :" << actionDescent.size() << endl;
  cout << "trajDescent descent size :" << trajDescent.size() << endl;
  cout << "grad Descent size :" << dAdqDescent.size() << endl;
  cout << "filtered grad Descent size :" << dAdqDescent_filt.size() << endl;
  jassert(actionDescent.size() == trajDescent.size());
  jassert(actionDescent.size() == dAdqDescent.size());
  jassert(actionDescent.size() == dAdqDescent_filt.size());
  jassert(actionDescent.size() == ham_descent.size());
  
  for (int iter=0; iter<actionDescent.size(); iter++)
  {
    for (int point=0; point<trajDescent.getUnchecked(iter).size(); point++)
    {
      historyFile << iter << "," << actionDescent.getUnchecked(iter) << "," << point;
      PhaseSpaceVec trajpq = trajDescent.getUnchecked(iter).getUnchecked(point);
      StateVec dAdq_local = dAdqDescent.getUnchecked(iter).getUnchecked(point);
      StateVec dAdq_filt_local = dAdqDescent_filt.getUnchecked(iter).getUnchecked(point);
      //cout << "trajectory size : " << trajpq.size() << endl;
      for (int m=0; m<trajpq.size()/2; m++)
        historyFile << "," << trajpq.getUnchecked(m);
      for (int m=trajpq.size()/2; m<trajpq.size(); m++)
        historyFile << "," << trajpq.getUnchecked(m);
      for (int m=0; m<dAdq_local.size(); m++)
        historyFile << "," << dAdq_local.getUnchecked(m);
      for (int m=0; m<dAdq_filt_local.size(); m++)
        historyFile << "," << dAdq_filt_local.getUnchecked(m);
      historyFile << "," << ham_descent.getUnchecked(iter).getUnchecked(point);
      historyFile << endl;
    } // end loop over points in current iteration
    //historyFile << endl;
  } // end loop over iterations
  
}









// update concentration curve as q^I = q^(I-1) - stepDescent * dAdq_filtered
void NEP::updateOptimalConcentrationCurve(Curve & _qcurve, double step)
{

  for (int k=0; k<nPoints->intValue(); k++)
  {
    // update curve point k component wise
    StateVec newqk;
    if (k==0 || k==nPoints->intValue()-1)
    {
      newqk = _qcurve.getUnchecked(k);
    }
    else
    {
      for (int m=0; m<_qcurve.getUnchecked(k).size(); m++)
      {
        newqk.add( _qcurve.getUnchecked(k).getUnchecked(m) - step * dAdq_filt.getUnchecked(k).getUnchecked(m) );
        //newqk.add( _qcurve.getUnchecked(k).getUnchecked(m) - stepDescent * dAdq_filt.getUnchecked(k).getUnchecked(m) );
        //newqk.add( qcurve.getUnchecked(k).getUnchecked(m) - stepDescent * dAdq.getUnchecked(k).getUnchecked(m) );
      }
    }
    _qcurve.setUnchecked(k, newqk);
    //qcurve.add(newqk);
  }
  //length_qcurve = curveLength(qcurve);
  //if (length_qcurve>0.)
  //  sampleRate = (double) nPoints->intValue() / length_qcurve;
  jassert(_qcurve.size() == nPoints->intValue());
  
}



//void NEP::calculateNewActionValue()
double NEP::calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t)
{
  //cout << "-- calculateAction() --" << endl;
  // check that pcurve, qcurve and tcurve have the same size
  jassert(qc.size() == pc.size());
  jassert(qc.size() == t.size());
  
  //cout << "--- calculate action along following curves ---" << endl;
  
  /*
  for (int point=0; point<nPoints; point++)
  {
    cout << "\npoint #" << point << endl;
    cout << "t = " << t.getUnchecked(point) << endl;
    cout << "q = ";
    for (auto & q : qc.getUnchecked(point))
      cout << q << " ";
    cout << endl;
    cout << "p = ";
    for (auto p  : pc.getUnchecked(point))
      cout << p << " ";
    cout << endl;
  }
  */
    
  Array<double> hamilt;
  for (int i=0; i<qc.size(); i++)
  {
    hamilt.add(evalHamiltonian(qc.getUnchecked(i), pc.getUnchecked(i)));
    //cout << "H(" << i << ") = " << evalHamiltonian(qc.getUnchecked(i), pc.getUnchecked(i)) << endl;
  }
  
  // use trapezoidal rule to calculate action = integral(0, T, p dq/dt - H)
  double newaction = 0.;
  for (int i=0; i<qc.size()-1; i++)
  {
    //cout << "at step " << i << endl;
    double deltaTi = t.getUnchecked(i+1) - t.getUnchecked(i);
    //cout << "\tdelta Ti = " << deltaTi << endl;
    // integrad at i
    double integrand = -0.5 * (hamilt.getUnchecked(i) + hamilt.getUnchecked(i+1)) * deltaTi;
    //integrand = 0.;
    
    jassert(pc.getUnchecked(i).size() == pc.getUnchecked(i+1).size()); // safety check
    jassert(qc.getUnchecked(i).size() == qc.getUnchecked(i+1).size());
    double spdebug = 0.;
    for (int m=0; m<qc.getUnchecked(i).size(); m++)
    {
      spdebug = pc.getUnchecked(i).getUnchecked(m)*(qc.getUnchecked(i+1).getUnchecked(m)-qc.getUnchecked(i).getUnchecked(m));
      double sp = 0.5 * (pc.getUnchecked(i).getUnchecked(m) + pc.getUnchecked(i+1).getUnchecked(m)) * (qc.getUnchecked(i+1).getUnchecked(m)-qc.getUnchecked(i).getUnchecked(m));
      integrand += sp;
      //cout << "\t(sp)_" << m << " = 1/2 * (" << pc.getUnchecked(i+1).getUnchecked(m) << "+" << pc.getUnchecked(i).getUnchecked(m);
      //cout << " * (" << qc.getUnchecked(i+1).getUnchecked(m) << "-" << qc.getUnchecked(i).getUnchecked(m) << ")" << " = " << sp << endl;
    }
    //cout << "p•dq = " << spdebug << "\tH_i "<< " = " << hamilt.getUnchecked(i) << endl;
    newaction += integrand;
    //cout << "\tadding " << integrand << endl;
  }
  
  //cout << "action = " << newaction << endl;
  // update action value
  //action = newaction;
  // keep track of action history
  //actionDescent.add(newaction);
  
  return newaction;
  
}


//double NEP::backTrackingMethodForStepSize(const Curve& qc, const Curve& dAdq)
double NEP::backTrackingMethodForStepSize(const Curve& qc)
{
  // init step with large value #para ?
  double step = stepDescentInitVal->floatValue();
  int timeout = 17; // (1/2)^17 < 1e-5, will trigger the loop to break
  
  //cout << "NEP::backTrackingMethodForStepSize" << endl;
  
  double currentaction = calculateAction(qc, g_pcurve, g_times);
  /* debugging
  cout << "current action = " << currentaction << endl;
  cout << "current q = " ;
  for (auto & qm : qc.getUnchecked(nPoints->intValue()/2))
    cout << qm << " ";
  cout << endl;
  cout << "deltaq = " ;
  for (auto & qm : deltaqc.getUnchecked(nPoints->intValue()/2))
    cout << qm << " ";
  cout << endl;
  cout << "p = " ;
  for (auto & pm : g_pcurve.getUnchecked(nPoints->intValue()/2))
    cout << pm << " ";
  cout << endl;
  cout << "t = " << g_times.getUnchecked(nPoints->intValue()/2) << endl;
  */
  
  StateVec nullvec;
  nullvec.insertMultiple(0, 0., simul->entities.size());
  int count = 0;
 
  for (int iter=0; iter<timeout; iter++)
  {
    if (step<1e-5)
    {
      break;
    }
    count++;
    
    // update concentration curve corresponding to current step
    Curve newcurve = qc;
    updateOptimalConcentrationCurve(newcurve, step);
    
    // find the corresponding lifted full trajectory, without updating global variables
    LiftTrajectoryOptResults liftResults = liftCurveToTrajectoryWithGSL(newcurve);
    
    /* debugging
    cout << "new q = ";
    for (auto & qm : newcurve.getUnchecked(nPoints->intValue()/2))
      cout << qm << " ";
    cout << endl;
    cout << "new p = " ;
    for (auto & pm : g_pcurve.getUnchecked(nPoints->intValue()/2))
      cout << pm << " ";
    cout << endl;
    cout << "new t = " << times.getUnchecked(nPoints->intValue()/2) << endl;
    */
    
    /*
    // sanity check
    for (int point=0; point<nPoints->intValue(); point++)
    {
      StateVec q = qc.getUnchecked(point);
      StateVec dq = deltaqc.getUnchecked(point);
      StateVec diff = newcurve.getUnchecked(point);
      cout << "step = " << step << endl;
      for (int m=0; m<q.size(); m++)
      {
        cout << q.getUnchecked(m) << " - " << dq.getUnchecked(m) << " = " << diff.getUnchecked(m) << endl;
      }
    }
    */
    
    // calculate action that would correspond to new concentration curve
    double newact = calculateAction(newcurve, liftResults.pcurve, liftResults.times);
    //cout << "iter = " << iter << ". step = " << step << ". new action = " << newact << " vs current action = " << currentaction << endl;
    if (newact>=currentaction)
    {
      //cout << "decreasing step" << endl;
      step *= 0.5; // hardcoded (1/2)^17 = 7.6e-6, should be enough
      //cout << "new step val = " << step << endl;
    }
    else
    {
      //cout << "exiting loop" << endl;
      break;
    }
  }
  //cout << "used = " << count << " iterations in backtracking method" << endl;
  
  if (step<1e-5)
    step = 0.;
  
  //LOGWARNING("backtracking algorithm did not converge to pick a descent step size. Returning 1e-6 as default value. Caution.");
  return step;
}


void NEP::applyButterworthFilter(juce::Array<double>& data, std::vector<juce::dsp::IIR::Filter<double>>& filters)
{
  for (int i = 0; i < data.size(); ++i)
  {
    double x = data[i];
    for (auto& f : filters)
      x = f.processSample(x);
    data.set(i, x);
  }
}

/*
//auto vector<juce::dsp::IIR::Filter<double>> makeFilters (coeffs)
vector<juce::dsp::IIR::Filter<double>> NEP::makeFilters(ReferenceCountedArray<IIRCoefficients> coeffs)
{
  vector<juce::dsp::IIR::Filter<double>> fs;
  for (auto& c : coeffs)
  {
    juce::dsp::IIR::Filter<double> f;
    for (size_t i=0; i<coeffs.size(); ++i)
        *chain.template get<i>().coefficients = *coeffs[i];
    //f.coefficients = c;
    fs.push_back(std::move(f));
  }
  return fs;
};

*/

void NEP::resampleInSpaceUniform(Array<StateVec>& signal, int size)
{
  if (signal.size()<2)
    return;
  
  /*
cout << "NEP::resampleInSpaceUniform()" << endl;
cout << "input = ";
for (int i=0; i<signal.size(); i++)
{
  for (int j=0; j<signal.getUnchecked(i).size(); j++)
  {
    string comma = (j==signal.getUnchecked(i).size()-1 ? "\n" : " , ");
    cout << signal.getUnchecked(i).getUnchecked(j) << comma;
  }
}
*/
  
  int dim = signal.getUnchecked(0).size();
  double dsize = (double) size;
  double L = curveLength(g_qcurve);
  
  // init newtraj
  Trajectory resampled_signal;
  resampled_signal.resize(size);
  for (int i=0; i<resampled_signal.size(); ++i)
  {
    StateVec nullvec;
    nullvec.insertMultiple(0, 0., dim);
    resampled_signal.setUnchecked(i, nullvec);
  }
 
  // resampling
  for (int i=0; i<signal.size(); i++)
  {
    // linear distance between 0 and g_qcurve length
    double l = 0. + (double)i * L/(dsize-1.);
    
    //cout << "i = " << i << endl;
    
    // find closest (left bound) index in space curve
    int closest = 0;
    Trajectory partial_curve;
    partial_curve.add(signal.getUnchecked(0));
    partial_curve.add(signal.getUnchecked(1));
    //cout << "npoints : " << g_qcurve.size() << ". partial curve has " << partial_curve.size() << " points" << endl;
    while (closest<size-1 && curveLength(partial_curve)<l)
    {
      closest++;
      partial_curve.add(signal.getUnchecked(closest+1));
    }
    //cout << "flga A" << endl;
    double l_pc_next = curveLength(partial_curve);
    //cout << "flga B" << endl;
    partial_curve.removeLast();
    //cout << "flga C" << endl;
    double l_pc = curveLength(partial_curve);
    
    if (i==0)
    {
      resampled_signal.setUnchecked(i, signal.getFirst());
    }
    else if (i==signal.size()-1)
    {
      resampled_signal.setUnchecked(i, signal.getLast());
    }
    else
    {
      // interpolate between q[closest] and q[closest+1]
      for (int m=0; m<signal.getUnchecked(0).size(); m++)
      {
        double alpha = (l-l_pc) / (l_pc_next-l_pc);
        double val = signal.getUnchecked(closest).getUnchecked(m) + alpha*(signal.getUnchecked(closest+1).getUnchecked(m)-signal.getUnchecked(closest).getUnchecked(m));
        resampled_signal.getReference(i).setUnchecked(m, val);
      } // end loop over dimension of the system
    } // end if
  }
  

  // modify input signal
  signal.resize(size);
  for (int i=0; i<signal.size(); i++)
  {
    signal.getUnchecked(i).insertMultiple(0, 0., dim);
    for (int j=0; j<signal.getUnchecked(i).size(); j++)
    {
      signal.getReference(i).setUnchecked(j, resampled_signal.getUnchecked(i).getUnchecked(j));
    }
  }
  /*
  cout << "NEP::resampleInTimeUniform()" << endl;
  cout << "output = ";
  for (int i=0; i<signal.size(); i++)
  {
    for (int j=0; j<signal.getUnchecked(i).size(); j++)
    {
      string comma = (j==signal.getUnchecked(i).size()-1 ? "\n" : " , ");
      cout << signal.getUnchecked(i).getUnchecked(j) << comma;
    }
  }
  */
  
  
}


void NEP::resampleInTimeUniform(Array<StateVec>& signal, int size)
{
  if (signal.size()<2)
    return;
  
  if (signal.size() != g_times.size())
  {
    LOGWARNING("Cannot resample in time uniform, array sizes do not match.");
    return;
  }
    /*
  cout << "NEP::resampleInTimeUniform()" << endl;
  cout << "input = ";
  for (int i=0; i<signal.size(); i++)
  {
    for (int j=0; j<signal.getUnchecked(i).size(); j++)
    {
      string comma = (j==signal.getUnchecked(i).size()-1 ? "\n" : " , ");
      cout << signal.getUnchecked(i).getUnchecked(j) << comma;
    }
  }
  */
  
  //int N = signal.size();
  int dim = signal.getUnchecked(0).size();
  double dsize =  (double) size;
  double ti = g_times.getFirst();
  double tf = g_times.getLast();
  
  // init newtraj
  Trajectory resampled_signal;
  resampled_signal.resize(size);
  for (int i = 0; i<resampled_signal.size(); ++i)
    resampled_signal.getReference(i).resize(dim);
  
  /*
  cout << "tvec : ";
  for (auto & el : g_times)
    cout << el << " ";
  cout << endl;
  */
  
  for (int i=0; i<signal.size(); i++)
  {
    // linear timing between ti and tf
    double t = ti + (double)i * (tf-ti)/(dsize-1.);
    
    // find closest index in time
    int closest = 0;
    while (closest < signal.size()-1 && g_times.getUnchecked(closest+1)<t)
      closest++;
    
   // cout << "closest = " << closest << " & signal.size = " << signal.size() << endl;
    
    if (i==0)
    {
      resampled_signal.setUnchecked(i, signal.getFirst());
    }
    else if (i==signal.size()-1)
    {
      resampled_signal.setUnchecked(i, signal.getLast());
    }
    else
    {
      // interpolate between q[closest] and q[closest+1]
      double alpha = (t-g_times.getUnchecked(closest)) / (g_times.getUnchecked(closest+1)-g_times.getUnchecked(closest));
      for (int m=0; m<signal.getUnchecked(0).size(); m++)
      {
        double val = signal.getUnchecked(closest).getUnchecked(m) + alpha*(signal.getUnchecked(closest+1).getUnchecked(m)-signal.getUnchecked(closest).getUnchecked(m));
        resampled_signal.getReference(i).setUnchecked(m, val);
      } // end loop over dimension of the system
    } // end if
  }
  

  // modify input signal
  for (int i=0; i<signal.size(); i++)
  {
    for (int j=0; j<signal.getUnchecked(i).size(); j++)
      signal.getReference(i).setUnchecked(j, resampled_signal.getUnchecked(i).getUnchecked(j));
  }
  
  /*
  cout << "NEP::resampleInTimeUniform()" << endl;
  cout << "output = ";
  for (int i=0; i<signal.size(); i++)
  {
    for (int j=0; j<signal.getUnchecked(i).size(); j++)
    {
      string comma = (j==signal.getUnchecked(i).size()-1 ? "\n" : " , ");
      cout << signal.getUnchecked(i).getUnchecked(j) << comma;
    }
  }
  */
  
  
}


void NEP::lowPassFiltering(Array<StateVec>& signal, bool isTimeUniform)
{
  if (signal.size() < 2 || g_times.size() < 2)
    return;
  
  int npoints = signal.size();
  int dim = signal.getFirst().size();
    
  // substract straight signal from input signal
  StateVec firstpoint = signal.getFirst();
  StateVec lastpoint = signal.getLast();
  /*
  cout << "NEP::lowPassFiltering() 1st point : ";
  for (auto & p : firstpoint)
    cout << p << " ";
  cout << endl;
  cout << "NEP::lowPassFiltering() last point : ";
  for (auto & p : lastpoint)
    cout << p << " ";
  cout << endl;
  */
  
  if (isTimeUniform)
  {
    cout << "input time :{ " << endl;
    for (int i=0; i<g_times.size(); i++)
    {
      string comma = ( i==g_times.size()-1 ? "};" : "," );
      cout << g_times.getUnchecked(i) << comma;
    }
    cout << endl;
    
    cout << "input signal : " << endl;
    for (int i=0; i<signal.size(); i++)
    {
      cout << "signal.add({";
      for (int j=0; j<signal.getUnchecked(i).size(); j++)
      {
        string comma = ( j==signal.getUnchecked(i).size()-1? "});" : "," );
        cout << signal.getUnchecked(i).getUnchecked(j) << comma;
      }
      cout << endl;
    }
  }
  
  
  // build a modified signal which uses the firstpoint as origin and unitary vector u as direction
  // x'_i = xlast + ( 1 - i/(N-1) ) ( xfirst - xlast )
  Trajectory signal2;
  Trajectory straightline;
  for (int i=0; i<npoints; i++)
  {
    StateVec point;
    StateVec slpoint;
    double alpha = double(i) / double(npoints-1.);
    if (isTimeUniform)
    {
      double ttot = g_times.getLast() - g_times.getFirst();
      if (ttot>0)
        alpha = (g_times.getUnchecked(i)-g_times.getFirst()) / (g_times.getLast() - g_times.getFirst());
      else
      {
        LOGWARNING("Total time along trajectory is null, time filtering uses space uniform sampling");
        cout << "t = ";
        for (auto &t : g_times)
          cout << t << " ";
        cout << endl;
      }
    }
    for (int m=0; m<dim; m++)
    {
      //double pprime = lastpoint.getUnchecked(m) + (1. - double(i) / double(npoints-1.)) *
      //(firstpoint.getUnchecked(m)-lastpoint.getUnchecked(m))
      
      double pprime = firstpoint.getUnchecked(m) + alpha * (lastpoint.getUnchecked(m)-firstpoint.getUnchecked(m));
      point.add(signal.getUnchecked(i).getUnchecked(m)-pprime);
      slpoint.add(pprime);
    }
    signal2.add(point);
    straightline.add(slpoint);
  }
  
  //cout << "NEP::lowPassFilering() -- symmetrize" << endl;
  
  // (anti)symmetrise signal
  Trajectory signal_sym;
  int nprime = 2*npoints-1;
  for (int u=0; u<nprime; u++)
  {
    StateVec point;
    for (int m=0; m<2; m++)
    {
      if (u<npoints-1)
        point.add(-1. * signal2.getUnchecked(npoints-u-1).getUnchecked(m));
      else
        point.add(signal2.getUnchecked(u-npoints+1).getUnchecked(m));
    }
    signal_sym.add(point);
  }
  
  //cout << "NEP::lowPassFilering() -- filter" << endl;
  
   
  // filtered trajectory init to be the symmetrized signal
  Trajectory signal2filter;
  for (auto & el : signal_sym)
    signal2filter.add(el);
  
  // actual filter
  
  // sampling rate set to 1 for filtering in space uniform
  float sr = 1.;
  if (isTimeUniform)
  {
    float timestep = g_times.getLast() / (float) (npoints-1.);
    if (timestep>0.)
      sr = 1./timestep;
    else
      LOGWARNING("time step is null --> sampling freq. = inf !! Use sampling rate of 1 by default, results should not be trusted.");
  }
  
  // interfaceUI gives max frequency in the signal. For instance 5 would mean any signal whose frequency is above 5 is suppressed.
  // this quantity is normalized to a sampling rate of 1.
  float juce_cutoffFreq = sr * cutoffFreq->floatValue();
  
  // if Nyquist condition is not met --> modify cutoff frequency, otherwise juce will complain
  if (juce_cutoffFreq >= sr/2.)
  {
    LOGWARNING("filtering above Nyquist frequency. Reducing cutoff freq. to Nyquist frequency.");
    juce_cutoffFreq = sr/2.;
    return;
  }

  // coeffs filtering
  auto coeffs = juce::dsp::FilterDesign<double>::designIIRLowpassHighOrderButterworthMethod(juce_cutoffFreq, sr, 4);
  
  // lambda function to get filters
  auto makeFilters = [&]()
  {
    std::vector<juce::dsp::IIR::Filter<double>> fs;
    for (auto& c : coeffs)
    {
      juce::dsp::IIR::Filter<double> f;
      f.coefficients = c;
      fs.push_back(std::move(f));
    }
    return fs;
  };
  
  
  for (int m=0; m<dim; m++)
  {
    Array<double> data;
    for (int i=0; i<signal2filter.size(); i++)
      data.add(signal2filter.getUnchecked(i).getUnchecked(m));
    
    // forward filter
    auto filters = makeFilters();
    applyButterworthFilter(data, filters);
    
    // reverse signal
    reverse(data.begin(), data.end());
    
    // backward filter
    filters = makeFilters();
    applyButterworthFilter(data, filters);
    
    // re-reverse signal
    std::reverse(data.begin(), data.end());
    /*
    for (int i=0; i<data.size(); ++i)
    {
      double x = data[i];
      for (auto& f : filters)
        x = f.processSample(x);
      data.set(i, x);
    }
    */
    
    // update original array
    for (int i=0; i<signal2filter.size(); i++)
      signal2filter.getReference(i).setUnchecked(m, data.getUnchecked(i));
      
  } // end loop over m
  
  // cout << "NEP::lowPassFilering() -- retrieve" << endl;
  
  // recover original signal filtered by taking only second half of symmetrized filtered signal
  for (int i=0; i<npoints; i++)
  {
    StateVec point;
    for (int m=0; m<dim; m++)
    {
      point.add( signal2filter.getUnchecked(i+npoints-1).getUnchecked(m) + straightline.getUnchecked(i).getUnchecked(m) );
      //point.add( straightline.getUnchecked(i).getUnchecked(m) );
    }
    if (i>0 && i<npoints-1) // do not modify first and last point of input signal
      signal.setUnchecked(i, point);
  }
  
  
} // end func







// using Méthod of Leapfrog / Störmer–Verlet instead of Euler Method
void NEP::nextStepHamiltonEoM(StateVec& q, StateVec& p, double dt_in, const bool forward, bool& shouldStop, Trajectory & traj)
{
  if (shouldStop)
    return;
  
  double thrshold = 1000.;
  double dt = (forward ? dt_in : -1.*dt_in);
  
  // save initial q and p in case that next step should not occur
  StateVec qi = q;
  StateVec pi = p;
  
  StateVec gradqH = evalHamiltonianGradientWithQ(q, p);
  if (norm2(gradqH)>thrshold) // cancel this step, reset to initial conditions
  {
    q = qi;
    p = pi;
    shouldStop = true;
    return;
  }
  // update p
  for (int m=0; m<q.size(); m++)
    p.setUnchecked(m, p.getUnchecked(m) - 0.5*dt*gradqH.getUnchecked(m));
  
  // calculate gradients w.r.t to p
  StateVec gradpH = evalHamiltonianGradientWithP(q, p);
  
  if (norm2(gradpH)>thrshold)
  {
    q = qi;
    p = pi;
    shouldStop = true;
    return;
  }
  
  // update q
  for (int m=0; m<q.size(); m++)
    q.setUnchecked(m, q.getUnchecked(m) + dt*gradpH.getUnchecked(m));
  
  // update gradients w.r.t to q
  gradqH = evalHamiltonianGradientWithQ(q, p);
  if (norm2(gradqH)>thrshold)
  {
    q = qi;
    p = pi;
    shouldStop = true;
    return;
  }
  
  // update p once more
  for (int m=0; m<q.size(); m++)
    p.setUnchecked(m, p.getUnchecked(m) - 0.5*dt*gradqH.getUnchecked(m));
  
  // add new (q ; p) point to the trajectory
  PhaseSpaceVec psv;
  for (int m=0; m<q.size(); m++)
  {
    psv.add(q.getUnchecked(m));
  }
  for (int m=0; m<p.size(); m++)
  {
    psv.add(p.getUnchecked(m));
  }
  traj.add(psv);
  
}


pair<Trajectory, Trajectory>  NEP::integrateHamiltonEquations(StateVec qi, StateVec pi)
{
 // dq/dt = dH/dp
 // dp/dt = -dH/dq
  double dt = 0.1;
  
  Trajectory traj_forward;
  Trajectory traj_backward;
  StateVec qcurrent_forward(qi);
  StateVec pcurrent_forward(pi);
  StateVec qcurrent_backward(qi);
  StateVec pcurrent_backward(pi);
  
  jassert(qi.size() == pi.size());
  bool break_forward = false;
  bool break_backward = false;
  
  //
  for (int st=0; st<1000; st++)
  {
    if (break_forward && break_backward)
      break;
    
    nextStepHamiltonEoM(qcurrent_forward, pcurrent_forward, dt, true, break_forward, traj_forward);
    nextStepHamiltonEoM(qcurrent_backward, pcurrent_backward, dt, false, break_backward, traj_backward);
    
  }
  
  pair<Trajectory, Trajectory> traj = make_pair(traj_forward, traj_backward); // one backward, one forward
  return traj;
  
  
}


void NEP::heteroclinicStudy()
{
  reset();

  // init concentration curve
  initConcentrationCurve();
  //testinitConcentrationCurve();
  // lift it to full (q ; p) space
  //liftCurveToTrajectoryWithNLOPT_old();
  liftCurveToTrajectoryWithGSL(g_qcurve);
  /*
  // read stable and unstable fixed points
  int sstI = sst_stable->intValue();
  int sstF = sst_saddle->intValue();
  StateVec qI, qF;
  qI.insertMultiple(0, 0., simul->entities.size());
  qF.insertMultiple(0, 0., simul->entities.size());
  for (auto & pairI : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstI).state)
  {
    qI.set(pairI.first->idSAT, pairI.second);
  }
  for (auto & pairF : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstF).state)
  {
    qF.set(pairF.first->idSAT, pairF.second);
  }
  */
  // define starting point for integrating hamilton equation of motion
  StateVec q_init;
  StateVec p_init;
  if (g_qcurve.size() > 1 && g_pcurve.size() > 1)
  {
    q_init = g_qcurve.getUnchecked(1);
    p_init = g_pcurve.getUnchecked(1);
  }
  else
  {
    LOG("Cannot perform heteroclinic study, concentration or momentum curves do not have enough points");
  }
  
  pair<Trajectory, Trajectory> trajs = integrateHamiltonEquations(q_init, p_init);
    
    // open output file
    String filename = "escape-paths_sst";
    filename += String(sst_stable->getValue().operator int()) + ".csv";
    ofstream historyFile;
    historyFile.open(filename.toStdString(), ofstream::out | ofstream::trunc);
    
    // first line
    historyFile << "point,forward";
    for (auto & ent : simul->entities)
      historyFile << ",q_" << ent->name;
    for (auto & ent : simul->entities)
      historyFile << ",p_" << ent->name;
    historyFile << endl;
    
    Trajectory trajfor = trajs.first;
    Trajectory trajback = trajs.second;
  
    // print forward trajectory
    for (int k=0; k<trajfor.size(); k++)
    {
      // print forward phase state vec ok iteration k
      historyFile << k << ",";
      historyFile << "1,";
      for (int m=0; m<trajfor.getUnchecked(k).size(); m++)
        historyFile << trajfor.getUnchecked(k).getUnchecked(m) << ",";
      historyFile << endl;
    }
    // print backward trajectory
    for (int k=0; k<trajback.size(); k++)
    {
      // print backward phase state vec ok iteration k
      historyFile << k << ",";
      historyFile << "0,";
      for (int m=0; m<trajback.getUnchecked(k).size(); m++)
        historyFile << trajback.getUnchecked(k).getUnchecked(m) << ",";
      historyFile << endl;
  }
  
}



void NEP::loadJSONData(var data, bool createIfNotThere)
{
  updateSteadyStateList();
  // call mother class
  ControllableContainer::loadJSONData(data);
}


/*
void NEP::newMessage(const Simulation::SimulationEvent &ev)
{
  switch (ev.type)
  {
    case Simulation::SimulationEvent::UPDATEPARAMS:
    {
      updateSteadyStateList();
    }
      break;
      
    case Simulation::SimulationEvent::WILL_START:
    {
    }
      break;
      
    case Simulation::SimulationEvent::STARTED:
    {
    }
      break;
      
    case Simulation::SimulationEvent::NEWSTEP:
    {
    }
      break;
      
    case Simulation::SimulationEvent::FINISHED:
    {
    }
      break;
  }
}


void NEP::newMessage(const ContainerAsyncEvent &e)
{

}
*/



double objective_max_p_debug(unsigned int n, const double* p_vec, double* grad, void* f_data)
{
  // retrieve encapsulated  variables
  EncapsVarForNLOpt * ev = static_cast<EncapsVarForNLOpt*>(f_data);
  
  // deltaq * p - H(p, q)
  double p = p_vec[0];
  //double lambda = p_vec[1];
  //double val = 1.*p - lambda*( 0.5*(p-1.)*(p-1.) -1.);
  double val = p * 1.;
  return val;
  /*
  // set momentum to its current value in optimization
  std::vector<double> p(p_vec, p_vec + n);
  // convert it to an Array<double> for legendre tranform calculation
  Array<double> pjuce;
  for (auto & val : p)
    pjuce.add(val);
  *ev->p = pjuce;
  
  
  cout << "[max_p] Called with p = ";
  for (unsigned i = 0; i < n; ++i)
  {
    cout << p[i] << " " << p_vec[i] << "  " << ev->p->getUnchecked(i) << "  ||  ";
  }
  cout << std::endl;
  
  
  
  double deltaT = 1.; // fix delta t for optimization its amplitude will be fixed later
  double lt = legendreTransform(ev, deltaT);
  return lt;
*/
 
 }

double constraint_debug(const vector<double> &x, vector<double> &grad, void* f_data)
{
  double p = x[0];
  double q = 1.;
  return 0.5*(p-1.)*(p-1.) + (q-2.)*(q-2.)*(q-2.);
}


struct Params
{
  double q;
  double dq;
};

int debugGSLresidual(const gsl_vector* x, void* params, gsl_vector* f)
{
    Params* param = static_cast<Params*>(params);

    double p = gsl_vector_get(x, 0);
    double dt = gsl_vector_get(x, 1);

    double H = 0.5 * (p-1.) * (p-1.) + (param->q - 2.0) * (param->q - 2.0) * (param->q - 2.0);
    double dHdp = (p-1.);

    gsl_vector_set(f, 0, H);
    gsl_vector_set(f, 1, param->dq - dt * dHdp);

    return GSL_SUCCESS;
}
/*
int debugGSL_fdf (gsl_vector * x, void * _p, gsl_matrix * f, gsl_matrix * J)
{
   Params * params = (Params*) _p;
   const double q = (params->q);
   const double dq = (params->dq);
   const double p = gsl_vector_get(x,0);
   const double dt = gsl_vector_get(x,1);

   const double u0 = exp(-x0);
   const double u1 = exp(-x1);

   gsl_vector_set (f, 0, A * x0 * x1 - 1);
   gsl_vector_set (f, 1, u0 + u1 - (1 + 1/A));

   gsl_matrix_set (J, 0, 0, A * x1);
   gsl_matrix_set (J, 0, 1, A * x0);
   gsl_matrix_set (J, 1, 0, -u0);
   gsl_matrix_set (J, 1, 1, -u1);
   return GSL_SUCCESS
}
*/


int ftest(const gsl_vector*, void*, gsl_vector*)
{
    return GSL_SUCCESS;
}


void NEP::debugNEPImplementation()
{
  
  cout << "NEP::debugNEPImplementation()" << endl;
  simul->affectSATIds();
  
  Trajectory qdebug;
  Trajectory pdebug;
  
  qdebug.add({1.00115, 1.00115});
  qdebug.add({1.12912, 1.01141});
  qdebug.add({1.25709, 1.02168});
  qdebug.add({1.38506, 1.03194});
  qdebug.add({1.51303, 1.04221});
  qdebug.add({1.64101, 1.05247});
  qdebug.add({1.76898, 1.06274});
  qdebug.add({1.89695, 1.07300});
  qdebug.add({2.02492, 1.08327});
  qdebug.add({2.15289, 1.09353});
  
  pdebug.add({0.00000, 0.00000});
  pdebug.add({0.00997, 0.00072});
  pdebug.add({0.00882, 0.00064});
  pdebug.add({0.00767, 0.00056});
  pdebug.add({0.00651, 0.00048});
  pdebug.add({0.00534, 0.00039});
  pdebug.add({0.00417, 0.00031});
  pdebug.add({0.00298, 0.00022});
  pdebug.add({0.00179, 0.00013});
  pdebug.add({0.00000, 0.00000});
  
  Array<double> tdebug;
  tdebug.add(0.00000);
  tdebug.add(86.60799);
  tdebug.add(163.59456);
  tdebug.add(230.95916);
  tdebug.add(288.70159);
  tdebug.add(336.82139);
  tdebug.add(375.31808);
  tdebug.add(404.19119);
  tdebug.add(423.44023);
  tdebug.add(433.06503);
  
  double act = calculateAction(qdebug, pdebug, tdebug);
  
  cout << "action debug = " << act << endl;
  
  return;
  
  /*
   
  // NLOPT BASIC IMPLEMETATION
   
  int n = 1;
  int nent = n;
  //nlopt::opt opt(nlopt::GN_DIRECT_L, nent);  // no gradient. #para. User could choose between different optimizers
  //nlopt::opt opt(nlopt::LN_COBYLA, nent);  //
  // apparently I should use cobyla
  // nlopt::LN_COBYLA
  
  // lower and upper bound for optimization
  vector<double> lowerbound_p(nent, -50.0); // #para
  vector<double> upperboundb_p(nent, 50.0);
  opt.set_lower_bounds(lowerbound_p);
  opt.set_upper_bounds(upperboundb_p);
  opt.set_maxeval(1000);    // nombre d’itérations max
  
  Array<double> opt_deltaT; // vector of optimal time assigned between each q(i) and q(i+1)
  Array<StateVec> opt_momentum; // vector of optimal momenta assigned between each q(i) and q(i+1)
  
  
  // assign first points along curve
  Array<double> nullP, dummyP;
  for (int i=0; i<Simulation::getInstance()->entities.size(); i++)
  {
    nullP.add(0.);
    dummyP.add(0.);
  }
  //opt_momentum.add(nullP);
  
  // loop over points in concentration space
  StateVec q0 = {0.5};
  StateVec q1 = {1.5};
  Curve qdebug;
  qdebug.add(q0);
  qdebug.add(q1);
  
  // q : q0 -- p0 -- q1 -- p1 --  .. -- qi -- pi -- q(i+1) -- pi -- ... qn(-1) -- p(n-1) -- qn
  //for (int k=0; k<g_qcurve.size()-1; k++) // n - 1 iterations
  for (int k=0; k<1; k++) // n - 1 iterations
  {
    //cout << "optimizing point #" << k << endl;
    StateVec q = qdebug.getUnchecked(k);
    StateVec qnext = qdebug.getUnchecked(k+1);
    jassert(q.size() == qnext.size());
    StateVec qcenter;
    Array<double> deltaq;
    for (int i=0; i<q.size(); i++)
    {
      deltaq.add(qnext.getUnchecked(i) - q.getUnchecked(i));
      qcenter.add( 0.5* (q.getUnchecked(i) + qnext.getUnchecked(i)));
    }
    
    // set maximization objective with respect to p variable
    EncapsVarForNLOpt * ev = new EncapsVarForNLOpt{&qcenter, &deltaq,  &dummyP, this};
    
    //opt.set_max_objective(objective_max_p, (void*)& deltaq);
    opt.set_max_objective(objective_max_p_debug, (void*) ev);
    opt.set_xtol_rel(1e-5);
    
    opt.add_equality_constraint(constraint_debug, (void*) ev, 1e-5);
    
    std::vector<double> p_opt(q.size(), 0.0); // init popt with null vector
    double maxH;
    
    cout << "will start optimization" << endl;
    
    // start optimization
    //nlopt::result result = opt.optimize(p_opt, maxH);
    try
    {
      //nlopt::result result = opt.optimize(p_opt, maxH);
      opt.optimize(p_opt, maxH);
      //std::cout << "Optimization success, result = " << result << std::endl;
    } catch (std::exception &e)
    {
      LOGWARNING("NLopt crashed with error message : " <<  e.what());
    }
    
    cout << "-- opt result --" << endl;
    cout << "p* = " << p_opt[0] << endl;
    //cout << "lambda* = " << p_opt[1] << endl;
    
    // assign time interval deduced from optimisation in p
    StateVec parr_opt;
    for (auto & pi : p_opt)
      parr_opt.add(pi);
    //StateVec gradpH = evalHamiltonianGradientWithP(qcenter, parr_opt);
    StateVec gradpH = {parr_opt[0]-1.};
    double norm2 = 0.;
    double deltaT = 0.;
    for (int i=0; i<gradpH.size(); i++)
    {
      norm2 += gradpH.getUnchecked(i) * gradpH.getUnchecked(i);
      deltaT += gradpH.getUnchecked(i) * deltaq.getUnchecked(i);
    }
    if (norm2>0.)
      deltaT /= norm2;
    else
    {
      LOGWARNING("gradient of hamiltonian in p has null norm, take results with caution.");
    }
  
    
    // add optimizing time
    //opt_deltaT.add(ev->t_opt);
    opt_deltaT.add(deltaT);
    
    // add optimizing momentum vector
    opt_momentum.add(parr_opt);
    
    cout << "p* = " << parr_opt[0] << endl;
    cout << "deltaT = " << deltaT << endl;
    
    //std::cout << "Optimal F(p, t*) = " << -maxf << std::endl;
  } // end loop over current trajectory
  
  cout << "finished optimizing" << endl;
  
  jassert(opt_deltaT.size() == opt_momentum.size());
  jassert(opt_deltaT.size() == nPoints->intValue()-1);
  
  // Build full trajectory in (q ; p) space from optima found previously
  //Array<double> tTraj;
  //Curve pTraj;
  //g_pcurve.clear();
  //g_times.clear();
  
  return;
  
*/
  /*
  const size_t n = 2;

  gsl_multiroot_function f;
  f.f = ftest;
  f.n = n;
  f.params = nullptr;

  gsl_vector* x = gsl_vector_alloc(n);
  gsl_vector_set_all(x, 0.0);

  const gsl_multiroot_fsolver_type* T = gsl_multiroot_fsolver_hybrids;

  gsl_multiroot_fsolver* s = gsl_multiroot_fsolver_alloc(T, n);

  gsl_multiroot_fsolver_set(s, &f, x);
  
  */
  /*
  StateVec qc = {0.5, 0.6};
  StateVec pc = {0.5, 0.6};
  //cout << "H(qc, pc) = " << evalHamiltonian(qc, pc) << endl;
  StateVec dHdp = evalHamiltonianGradientWithP(qc, pc);
  cout << "dH/dp = ";
  for (auto & el : dHdp)
    cout << el << " ";
  cout << endl;
  
  StateVec dHdq = evalHamiltonianGradientWithQ(qc, pc);
  cout << "dH/dq = ";
  for (auto & el : dHdq)
    cout << el << " ";
  cout << endl;
  
  dsp::Matrix<double> hess = evalHamiltonianHessianWithP(qc, pc);
  cout << "d^2H/dp2 = \n";
  for (int i=0; i<hess.getSize().getUnchecked(0); i++)
  {
    for (int j=0; j<hess.getSize().getUnchecked(1); j++)
    {
      cout << hess(i,j) << " ";
    }
    cout << endl;
  }
  cout << endl;
  
  */
  /*
  // create curve to filter = straight line with noise around it.
  StateVec firstpoint = {1.00115,1.00115};
  StateVec lastpoint = {2.15525,1.09354};
  Trajectory traj;
  int N = 5; double NN = (double) N;
  double stepX = (lastpoint.getUnchecked(0) - firstpoint.getUnchecked(0)) / NN;
  double stepY = (lastpoint.getUnchecked(1) - firstpoint.getUnchecked(1)) / NN;
  StateVec step; step.add(stepX); step.add(stepY);
  Trajectory straightline;
  for (int i=0; i<=50; i++)
  {
    StateVec slpoint;
    for (int m=0; m<2; m++)
    {
      double c = firstpoint.getUnchecked(m) + (double) i / NN * (lastpoint.getUnchecked(m) - firstpoint.getUnchecked(m));
      //double crand = c;
      slpoint.add(c);
    }
    straightline.add(slpoint);
  }
  
  for (int i=0; i<straightline.size(); i++)
  {
    StateVec q = stri
    
  }
  */
  
}



void applyButterworthDebug(juce::Array<double>& data, std::vector<juce::dsp::IIR::Filter<double>>& filters)
{
    for (int i = 0; i < data.size(); ++i)
    {
        double x = data[i];
        for (auto& f : filters)
            x = f.processSample(x);

        data.set(i, x);
    }
}

void NEP::debugFiltering()
{
  state = Idle;
  cout << "debugFiltering" << endl;
  
  g_times = {0,0.919079,1.25637,1.47272,1.63751,1.77431,1.89395,2.00241,2.10337,2.19929,2.29196,2.38276,2.47283,2.56318,2.65477,2.74857,2.84562,2.9471,3.05441,3.16926,3.29379,3.43083,3.5842,3.75937,3.96456,4.21306,4.52856,4.95972,5.63383,7.21447};
  
  Array<Array<double>> signal;
  signal.add({1.00115,1.00115});
  signal.add({1.01176,1.00263});
  signal.add({1.02236,1.0041});
  signal.add({1.03296,1.00558});
  signal.add({1.04917,1.00777});
  signal.add({1.0781,1.01159});
  signal.add({1.12364,1.01714});
  signal.add({1.18835,1.02384});
  signal.add({1.2729,1.03017});
  signal.add({1.37455,1.03435});
  signal.add({1.48443,1.03664});
  signal.add({1.593,1.03929});
  signal.add({1.69222,1.04406});
  signal.add({1.7782,1.0506});
  signal.add({1.85011,1.05768});
  signal.add({1.90931,1.06434});
  signal.add({1.95735,1.07011});
  signal.add({1.99611,1.07489});
  signal.add({2.02706,1.07873});
  signal.add({2.05139,1.08173});
  signal.add({2.07352,1.08445});
  signal.add({2.08801,1.08621});
  signal.add({2.1025,1.08796});
  signal.add({2.11415,1.08934});
  signal.add({2.12061,1.09004});
  signal.add({2.12706,1.09074});
  signal.add({2.13352,1.09143});
  signal.add({2.13997,1.09213});
  signal.add({2.14643,1.09283});
  signal.add({2.15289,1.09353});
  
  // open output file
  String fn = "./debug/debug-time-uniform-filtering.csv";
  ofstream hF;
  hF.open(fn.toStdString(), ofstream::out | ofstream::trunc);
  
  // print input signal to file
  hF << "isFilt,point,time,q_X1,q_X2" << endl;
  for (int i=0; i<signal.size(); i++)
  {
    hF << false << "," << i << "," << g_times.getUnchecked(i) << "," << signal.getUnchecked(i).getUnchecked(0) << "," << signal.getUnchecked(i).getUnchecked(1) << endl;
  }
  
  // filter
  lowPassFiltering(signal, 1);
  
  // print output signal to file
  for (int i=0; i<signal.size(); i++)
  {
    hF << true << "," << i << "," << g_times.getUnchecked(i) << "," << signal.getUnchecked(i).getUnchecked(0) << "," << signal.getUnchecked(i).getUnchecked(1) << endl;
  }
  
  
  return;
  
  
  

  mt19937 rng(std::random_device{}()); // moteur Mersenne Twister
  
  cout << "NEP::debugFilering() -- create curve" << endl;

  // create curve to filter = straight line with noise around it.
  StateVec firstpoint = {1.00115,1.00115};
  StateVec lastpoint = {2.15525,1.09354};
  Trajectory traj;
  int N = 50; double NN = (double) N;
  double stepX = (lastpoint.getUnchecked(0) - firstpoint.getUnchecked(0)) / NN;
  double stepY = (lastpoint.getUnchecked(1) - firstpoint.getUnchecked(1)) / NN;
  StateVec step; step.add(stepX); step.add(stepY);
  Trajectory straightline;
  for (int i=0; i<=50; i++)
  {
    StateVec point;
    StateVec slpoint;
    for (int m=0; m<2; m++)
    {
      double c = firstpoint.getUnchecked(m) + (double) i / NN * (lastpoint.getUnchecked(m) - firstpoint.getUnchecked(m));
      double interval = 0.5*step.getUnchecked(m);
      if (m==1)
        interval *= 1.;
      uniform_real_distribution<double> dist(c-interval, c+interval);
      double crand = dist(rng);
      //double crand = c;
      point.add(crand);
      slpoint.add(c);
    }
    traj.add(point);
    straightline.add(slpoint);
  }
  
  cout << "NEP::debugFilering() -- remove straight line" << endl;
  
  // remove straightline to signal.
  Trajectory traj2;
  for (int i=0; i<=50; i++)
  {
    StateVec point;
    for (int m=0; m<2; m++)
    {
      point.add(traj.getUnchecked(i).getUnchecked(m) - straightline.getUnchecked(i).getUnchecked(m));
    }
    traj2.add(point);
  }
  
  cout << "NEP::debugFilering() -- symmetrize" << endl;
  
  // symmetrise signal
  Trajectory traj_sym;
  int Nprime = 2*N-1;
  for (int u=0; u<Nprime; u++)
  {
    StateVec point;
    for (int m=0; m<2; m++)
    {
      if (u<N-1)
        point.add(-1. * traj2.getUnchecked(N-u-1).getUnchecked(m));
      else
        point.add(traj2.getUnchecked(u-N+1).getUnchecked(m));
    }
    traj_sym.add(point);
  }
  
  cout << "NEP::debugFilering() -- filter" << endl;
  
   
  // filtered trajectory init to be the symmetrized signal
  Trajectory traj2filter;
  for (auto & el : traj_sym)
    traj2filter.add(el);
  
  // actual filter
  
  //float sr = (float) curveLength(traj2filter) / float(traj2filter.size());
  float sr = 1.;

  float jucefreq = cutoffFreq->floatValue() / (float) N; // wrong, should be sampling rate / minPeriodInSample
  // careful ! cutoff freq cannot exceed fqnyst. 0 < cutofffreq < samplingrate/2
  auto coeffs = juce::dsp::FilterDesign<double>::designIIRLowpassHighOrderButterworthMethod(jucefreq, sr, 4);
  
  auto makeFilters = [&]() {
          std::vector<juce::dsp::IIR::Filter<double>> fs;
          for (auto& c : coeffs) {
              juce::dsp::IIR::Filter<double> f;
              f.coefficients = c;
              fs.push_back(std::move(f));
          }
          return fs;
      };
  
  cout << "Setting filter with cutoff Freq : " << jucefreq << ". and sampling rate : " << sr << endl;
  /*
  vector<juce::dsp::IIR::Filter<double>> filters;
  for (auto& c : coeffs)
  {
      juce::dsp::IIR::Filter<double> f;
      f.coefficients = c;
      filters.push_back(std::move(f));
  }
  */
  
  for (int m=0; m<2; m++)
  {
    Array<double> data;
    for (int i=0; i<traj2filter.size(); i++)
      data.add(traj2filter.getUnchecked(i).getUnchecked(m));
    
    // forward filter
    auto filters = makeFilters();
    applyButterworthDebug(data, filters);
    
    // reverse signal
    reverse(data.begin(), data.end());
    
    // backward filter
    filters = makeFilters();
    applyButterworthDebug(data, filters);
    
    // re-reverse signal
    std::reverse(data.begin(), data.end());
    /*
    for (int i=0; i<data.size(); ++i)
    {
      double x = data[i];
      for (auto& f : filters)
        x = f.processSample(x);
      data.set(i, x);
    }
    */
    
    // update original array
    for (int i=0; i<traj2filter.size(); i++)
      traj2filter.getReference(i).setUnchecked(m, data.getUnchecked(i));
      
  }
  
  
  
  cout << "NEP::debugFilering() -- retrieve" << endl;
  
  // retrieve original signal filtered
  Trajectory filtered_traj;
  for (int i=0; i<N; i++)
  {
    StateVec point;
    for (int m=0; m<2; m++)
    {
      point.add( traj2filter.getUnchecked(i+N-1).getUnchecked(m) + straightline.getUnchecked(i).getUnchecked(m) );
      //point.add( straightline.getUnchecked(i).getUnchecked(m) );
    }
    filtered_traj.add(point);
  }
  
  cout << "NEP::debugFilering() -- write file 1" << endl;
  
  // open output file
  String filename = "./debug/debug-filtering.csv";
  ofstream historyFile;
  historyFile.open(filename.toStdString(), ofstream::out | ofstream::trunc);
  
  historyFile << "point";
  for (auto & ent : simul->entities)
    historyFile << ",q_" << ent->name << ",qprime_" << ent->name << ",qfilt_" << ent->name;
  historyFile << endl;


    for (int point=0; point<N; point++)
    {
      historyFile << point;
      StateVec q = traj.getUnchecked(point);
      StateVec q2 = traj2.getUnchecked(point);
      StateVec qfilt = filtered_traj.getUnchecked(point);
      
      for (int m=0; m<q.size(); m++)
      {
        historyFile << "," << q.getUnchecked(m) << "," << q2.getUnchecked(m) << "," << qfilt.getUnchecked(m);
      }
      historyFile << endl;
    } // end loop over points in current iteration
    //historyFile << endl;
  
  // also save symmetrized signal
  cout << "NEP::debugFilering() -- write file 2" << endl;
  
  String filename2 = "./debug/debug-filtering2.csv";
  ofstream historyFile2;
  historyFile2.open(filename2.toStdString(), ofstream::out | ofstream::trunc);
  
  historyFile2 << "point";
  for (auto & ent : simul->entities)
    historyFile2 << ",qsym_" << ent->name << ",qsymfilt_" << ent->name;
  historyFile2 << endl;
  
  
  for (int point=0; point<Nprime; point++)
  {
    historyFile2 << point;
    StateVec q = traj_sym.getUnchecked(point);
    StateVec q2 = traj2filter.getUnchecked(point);
    
    for (int m=0; m<q.size(); m++)
    {
      historyFile2 << "," << q.getUnchecked(m) << "," << q2.getUnchecked(m);
    }
    historyFile2 << endl;
  } // end loop over points in current iteration
  
  
  
  cout << "END debugFiltering" << endl;
  state = Idle;
  
}
