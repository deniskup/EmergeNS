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
  
  kinetics = new KineticLaw(false, 0.);
  


  
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
  simul->affectSATIds();
  reset();

  // has bad behavior for now, trajectory eventually diverges
  // need deeper understanding
  // see https://web.pa.msu.edu/people/dykman/pub06/jcp100_5735.pdf
  if (heteroclinic_study)
  {
    LOG("heteroclinic study not implemented yet, return.");
    return;
    //heteroclinicStudy();
    //heteroclinic_study = false;
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
  LOG("init g_qcurve");
  initConcentrationCurve(false);
  
  // message to async
  nepNotifier.addMessage(new NEPEvent(NEPEvent::WILL_START, this));
  
  int count = 0;
  while (descentShouldContinue(count+1) && !threadShouldExit())
  {
    count++;
    if (count==1)
      LOG("initial value of action = " + to_string(action));
    LOG("\niteration #" + to_string(count));
    
    if (count>1)
    {
      stepDescent = backTrackingMethodForStepSize(g_qcurve);
      //cout << "using step = " << stepDescent << endl;
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
    LOG("lifting trajectory");
    //LiftTrajectoryOptResults liftoptres = liftCurveToTrajectoryWithNLOPT();
    LiftTrajectoryOptResults liftoptres = liftCurveToTrajectoryWithGSL(g_qcurve);
    
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
    LOG("calculating action");
    double newaction = calculateAction(g_qcurve, g_pcurve, g_times);
    double diffAction = action - newaction;
    actionDescent.add(newaction);
    action = newaction;
    
    if (maxPrinting->boolValue())
    {
      debugfile << "-- Action --" << endl;
      debugfile << "S = " << newaction << " & deltaS = " << diffAction << endl;
    }
    
    LOG("action = " + to_string(newaction) + ". deltaS = " + to_string(diffAction));
    
    // message to async to monitor the descent
    nepNotifier.addMessage(new NEPEvent(NEPEvent::NEWSTEP, this, count, newaction, cutoffFreq->floatValue(), nPoints->intValue(), metric)); 
    
    
    // check algorithm descent status
    bool shouldUpdate = descentShouldUpdateParams(diffAction);
    if (shouldUpdate && count>1)
    {
      LOG("descentUpdatesParams");
      updateDescentParams();
      
      // the following I do not perfor
      //resampleInTimeUniform(g_qcurve, g_qcurve.size());
      //lowPassFiltering(g_qcurve, true);
      //resampleInSpaceUniform(g_qcurve, g_qcurve.size());
      //liftCurveToTrajectoryWithGSL();
      
      // increase sampling of concentration curve is optionnal. Not implemented at the moment.
      //continue; // next iteration using the filtered g_qcurve
    }
    
    
    // dA / dq
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
        
  } // end while
  
  //cout << actionDescent.size() << " --- " << trajDescent.size() << endl;
  
  // save descent algorithm results into a file
  LOG("writing descent to file");
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
  //cout << "input qcurve size = " << qcurve.size() << endl;
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


void NEP::initConcentrationCurve(bool useDeterministicTrajectory)
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
  
  // init q curve
  g_qcurve.clear();
  double NN = (double) nPoints->intValue();
  jassert(nPoints->intValue()>1);
  
  if (useDeterministicTrajectory)
  {
    // copy the entities and reactions from simulation instance
    OwnedArray<SimEntity> entities;
    OwnedArray<SimReaction> reactions;
    entities.clear();
    reactions.clear();
    
    // If has not been called yet, the copy will not work properly
    simul->affectSATIds();
    
    // fill entity array with copies of the ones present in the simulation instance
    for (auto & ent : simul->entities)
      entities.add(ent->clone().release());
    
    for (auto & ent : entities)
    {
      ent->entity = nullptr; // just make sure this copied SimEntity will not interfere with Entity object
      ent->concent.resize(1);
      ent->previousConcent.resize(1);
      ent->startConcent.resize(1);
      ent->deterministicConcent.resize(1);
    }
    
    for (auto & r : simul->reactions)
    {
      Array<SimEntity*> reactants;
      Array<SimEntity*> products;
      for (auto & e : r->reactants)
      {
        reactants.add(entities[e->idSAT]);
      }
      for (auto & e : r->products)
      {
        products.add(entities[e->idSAT]);
      }
      SimReaction * copyr = new SimReaction(reactants, products, r->assocRate ,  r->dissocRate,  r->energy);
      reactions.add(copyr);
    }
    
    jassert(entities.size() == simul->entities.size());
    jassert(reactions.size() == simul->reactions.size());
    
    // set first point of qcurve = qF
    g_qcurve.add(qF);
    
    // set initial concentration of entities to be very close from qF in the direction of qI
    Curve sl = {qI, qF};
    double L = curveLength(sl);
    jassert(L>0.);
    for (int i=0; i<qI.size(); i++)
    {
      float ui = qF.getUnchecked(i) + 0.01 * ( qI.getUnchecked(i)-qF.getUnchecked(i) ) / L;
      entities[i]->concent.setUnchecked(0, ui);
      //entities[i]->startConcent.setUnchecked(0, ui);
    }
    
    
    // deterministic dynamics of the system until a stationnary state is reached
    float distance = 1000.;
    float precision = 1e-5;
    int timeout = simul->dt->floatValue() * 50000;
    float t = 0.;
    int count = 0;
    bool delay = true; // require the deterministic search to run a minimum amount of time
    // otherwise, too close from an unstable steady state, variation might be too small
    while (distance>precision || delay)
    {
      count++;
      t += simul->dt->floatValue();
      if (t>100.) // free the boolean delay
        delay = false;
      if (t>timeout)
        break;
      // deterministic traj
      kinetics->SteppingReactionRates(reactions, simul->dt->floatValue(), 0, false);
      kinetics->SteppingInflowOutflowRates(entities, simul->dt->floatValue(), 0);
      
      // update concentration values of entities
      for (auto & ent : entities)
      {
        ent->refresh();
      }
      
      // add new value to global qcurve
      StateVec qi;
      for (int k=0; k<entities.size(); k++)
        qi.add(entities[k]->concent.getUnchecked(0));
      g_qcurve.add(qi);
      
      // calculate variation in last dt
      distance = 0.;
      for (auto & ent : entities)
      {
        float deltaC = ent->concent.getUnchecked(0)-ent->previousConcent.getUnchecked(0);
        distance += deltaC*deltaC;
      }
      distance = sqrt(distance);
    } // end while
    
    // set last point of qcurve = qI
    g_qcurve.add(qI);
    
    // resample qcurve
    resampleInSpaceUniform(g_qcurve, nPoints->intValue());
  }
  else // use straightline
  {
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

// #HERE extremely slow, but seems to work though.
void NEP::resampleInSpaceUniform(Array<StateVec>& signal, int newsize)
{
  if (signal.size()<2 || newsize<2)
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
  double d_newsize = (double) newsize;
  double L = curveLength(signal);
  
  // init newtraj with null vectors
  Trajectory resampled_signal;
  resampled_signal.resize(newsize);
  for (int i=0; i<newsize; ++i)
  {
    StateVec nullvec;
    nullvec.insertMultiple(0, 0., dim);
    resampled_signal.setUnchecked(i, nullvec);
  }
  
  // cumulative lengths of input signals
  Array<double> cumulative_lengths;
  cumulative_lengths.insertMultiple(0, 0., signal.size());
  for (int k=1; k<signal.size(); k++)
  {
    Trajectory segment({signal.getUnchecked(k-1), signal.getUnchecked(k)});
    cumulative_lengths.setUnchecked(k, cumulative_lengths.getUnchecked(k-1) + curveLength(segment));
  }
  
  //cout << "input signal length = " << L << endl;
 
  // resampling
  int last_closest = 0;
  for (int i=0; i<newsize; i++)
  {
    // linear distance between 0 and signal length
    double li = 0. + (double)i * L/(d_newsize-1.);
    
    //cout << "i = " << i << ". l_i = " << 100.*li/L << "%" << endl;
    
    // find closest matching index in cumulative length array
    auto it = lower_bound(cumulative_lengths.begin(), cumulative_lengths.end(), li);
    int closest = (int) distance(cumulative_lengths.begin(), it) - 1;
    closest = max(0, min(closest, (int)signal.size()-2)); // make sure closest is properly bounded
    
    // linear interpolation
    double l_inf = cumulative_lengths.getUnchecked(closest);
    double l_sup = cumulative_lengths.getUnchecked(closest+1);
    double alpha = (l_sup != l_inf) ? (li - l_inf) / (l_sup - l_inf) : 0.0;
    alpha = max(0., min(1., alpha));
    
    // keep track of current finding to accelerate next iteration
    last_closest = closest;
    
    //cout << "closest : " << closest << ". linf = " << 100.*l_inf/L << "% & lsup = " << 100*l_sup/L << "%" << endl;
    
    if (i==0)
    {
      resampled_signal.setUnchecked(i, signal.getFirst());
    }
    else if (i==newsize-1)
    {
      resampled_signal.setUnchecked(i, signal.getLast());
    }
    else
    {
      // interpolate between q[closest] and q[closest+1]
      for (int m=0; m<dim; m++)
      {
        double val = signal.getUnchecked(closest).getUnchecked(m) + alpha*(signal.getUnchecked(closest+1).getUnchecked(m)-signal.getUnchecked(closest).getUnchecked(m));
        resampled_signal.getReference(i).setUnchecked(m, val);
      } // end loop over dimension of the system
    } // end if
  }
  

  // modify input signal
  signal.resize(newsize);
  for (int i=0; i<newsize; i++)
  {
    signal.getReference(i).clear();
    signal.getReference(i).insertMultiple(0, 0., dim);
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
  cout << endl;
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
  initConcentrationCurve(false);
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
