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



//double objective_max_p(const Array<double>& p_vec, Array<double>& grad, void* f_data)
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
  
  /*
  cout << "[max_p] Called with p = ";
  for (unsigned i = 0; i < n; ++i)
  {
    cout << p[i] << " " << p_vec[i] << "  " << ev->p->getUnchecked(i) << "  ||  ";
  }
  cout << std::endl;
  */
  
  
  double deltaT = 1.; // fix delta t for optimization its amplitude will be fixed later
  double lt = legendreTransform(ev, deltaT);
  return lt;

 
 }
 


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

  cutoffFreq = addFloatParameter("Cutoff frequency", "frequency of low-pass filtering used by the descent algorithm", 4.);

  maxcutoffFreq = addFloatParameter("Max. cutoff frequency", "max. frequency of low-pass filtering, after what descent will stop.", 100.);
  
  action_threshold = addFloatParameter("Action threshold", "Descent will stop when action threshold is reached", 0.01);
  
  timescale_factor = addFloatParameter("Time scale factor", "Descent behaves badly when kinetics rate constants are too low. A solution consists in scaling up those constants.", 100.);
  
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
  qcurve.clear();
  pcurve.clear();
  times.clear();
  dAdq.clear();
  dAdq_filt.clear();
  action = 10.;
  length_qcurve = 0.;
  stepDescent = 1.;
  //cutoffFreq TODO : should reset as well ?
}


void NEP::stop()
{
  state = Idle;
  cout << "[DEBUG] stop() NEP state = " << state << endl;
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

  
  
/*
   // study to plot dA/dq for initial qcurve
  
  cout << "init concentration curve" << endl;
  // init concentration trajectory
  initConcentrationCurve();
  LiftTrajectoryOptResults liftoptres = liftCurveToTrajectory();
  
  // plot dA / dq
  Array<StateVec> dAdq;
  for (int point=0; point<nPoints->intValue(); point++)
  {
    StateVec dHdqk = evalHamiltonianGradientWithQ(qcurve.getUnchecked(point), pcurve.getUnchecked(point));
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
    
    StateVec dAdqk;
    for (int m=0; m<dHdqk.size(); m++)
    {
      dAdqk.add(-dHdqk.getUnchecked(m) - dpdtk.getUnchecked(m));
    }
    
    dAdq.add(dAdqk);
  }
  
  // open output file
  String filename = "dAdq.csv";
  ofstream historyFile;
  historyFile.open(filename.toStdString(), ofstream::out | ofstream::trunc);
  historyFile << "point,X1,X2,dA/dX1,dA/dX2" << endl;
  for (int point=0; point<nPoints->intValue(); point++)
  {
    historyFile << point;
    for (auto & q : qcurve.getUnchecked(point))
      historyFile << "," << q ;
    for (auto & da : dAdq.getUnchecked(point))
      historyFile << "," << da;
    historyFile << endl;
  }
  
*/
  
  if (debug)
  {
    debugfile.open("DEBUG.txt", ofstream::out | ofstream::trunc);
    debugfile << "\t\t\t------ DEBUG ------" << endl;
    debugfile << "Descent parameters" << endl;
    debugfile << "sampling points : " << nPoints->intValue() << endl;
  }
  
  // init concentration curve
  cout << "init qcurve" << endl;
  initConcentrationCurve();
  
  int count = 0;
  nepNotifier.addMessage(new NEPEvent(NEPEvent::WILL_START, this));
  //while (count < Niterations->intValue() && !threadShouldExit())
  while (descentShouldContinue(count+1) && !threadShouldExit())
  {
    count++;
    if (count==1)
      cout << "initial value of action = " << action << endl;
    cout << "iteration #" << count << endl;
    
    if (count>1)
    {
      stepDescent = backTrackingMethodForStepSize(qcurve, dAdq_filt);
      updateOptimalConcentrationCurve();
    }
    
    if (debug)
    {
      debugfile << "\nIteration " << count << endl;
      debugfile << "-- concentration curve --" << endl;
      for (int p=0; p<nPoints->intValue(); p++)
      {
        debugfile << "(";
        int c=0;
        for (auto & qm : qcurve.getUnchecked(p))
        {
          string comma = (c == qcurve.getUnchecked(p).size()-1 ? ") " : ",");
          debugfile << qm << comma ;
          c++;
        }
      }
      debugfile << endl;
    }
    
    // lift current trajectory to full (q ; p; t) space
    // this function updates global variables pcurve and times
    cout << "lifting trajectory" << endl;
    LiftTrajectoryOptResults liftoptres = liftCurveToTrajectory();
    
    // keep track of trajectory update in (q ; p) space
    Trajectory newtraj;
    for (int point=0; point<nPoints->intValue(); point++)
    {
      PhaseSpaceVec psv;
      for (auto & qm : qcurve.getUnchecked(point))
        psv.add(qm);
      for (auto & pm : pcurve.getUnchecked(point))
        psv.add(pm);
      newtraj.add(psv);
    }
    //cout << "adding a trajectory of size : " << newtraj.size() << " = " << qcurve.size() << " + " << pcurve.size() << endl;
    trajDescent.add(newtraj);
    
    if (debug)
    {
      debugfile << "-- momentum curve --" << endl;
      for (int p=0; p<nPoints->intValue(); p++)
      {
        debugfile << "(";
        int c=0;
        for (auto & pm : pcurve.getUnchecked(p))
        {
          string comma = (c == pcurve.getUnchecked(p).size()-1 ? ") " : ",");
          debugfile << pm << comma ;
          c++;
        }
      }
      debugfile << endl;
    }
  
    
    // calculate action value
    cout << "calculating action" << endl;
    double newaction = calculateAction(qcurve, pcurve, times);
    double diffAction = abs(action - newaction);
    //actionDescent.add(diffAction);
    actionDescent.add(newaction);
    
    if (debug)
    {
      debugfile << "-- Action --" << endl;
      debugfile << "S = " << newaction << " & deltaS = " << diffAction << endl;
    }
    
    // message to async to monitor the descent
    cout << "in NEP : " << newaction << ". abs diff = " << diffAction << endl;
    nepNotifier.addMessage(new NEPEvent(NEPEvent::NEWSTEP, this, count, newaction, cutoffFreq->floatValue(), nPoints->intValue(), metric));
    
    
    // check algorithm descent status
    bool shouldUpdate = descentShouldUpdateParams(diffAction);
    if (shouldUpdate && count>1)
    {
      updateDescentParams();
      filterConcentrationTrajectory(); //TODO : in gagrani & smith here they use a time parametrization
      stepDescent = 1.;
      // increase sampling of concentration curve is optionnal. Not implemented at the moment.
      //continue; // next iteration using the filtered qcurve
    }
    
    
    // dA / dq
//    Array<StateVec> dAdq;
    for (int point=0; point<nPoints->intValue(); point++)
    {
      StateVec dHdqk = evalHamiltonianGradientWithQ(qcurve.getUnchecked(point), pcurve.getUnchecked(point));
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
      
      StateVec dAdqk;
      for (int m=0; m<dHdqk.size(); m++)
      {
        dAdqk.add(-dHdqk.getUnchecked(m) - dpdtk.getUnchecked(m));
      }
      
      dAdq.add(dAdqk);
    }
    dAdqDescent.add(dAdq);
    
    // filtered gradient
    dAdq_filt = dAdq;
    filter.setSamplingRate(sampleRate);
    filter.setCutoffFrequency(cutoffFreq->floatValue());
    filter.process(dAdq_filt);
    dAdqDescent_filt.add(dAdq_filt);
    
    if (debug)
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
    // this function update global variable qcurve
    //updateOptimalConcentrationCurve_old(liftoptres.opt_momentum, liftoptres.opt_deltaT);
        
    
  } // end while
  
  cout << actionDescent.size() << " --- " << trajDescent.size() << endl;
  
  // save descent algorithm results into a file
  cout << "writing to file" << endl;
  writeDescentToFile();
  
  stop();
  
  
}




LiftTrajectoryOptResults NEP::liftCurveToTrajectory()
{
  int nent = Simulation::getInstance()->entities.size();
  //nlopt::opt opt(nlopt::LD_LBFGS, nent);  // momentum is nentities dimensionnal
  //nlopt::opt opt(nlopt::LN_COBYLA, nent);  // momentum is nentities dimensionnal
  nlopt::opt opt(nlopt::GN_DIRECT_L, nent);  // no gradient. #para. User could choose between different optimizers
  

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
    StateVec q = qcurve.getUnchecked(k);
    StateVec qnext = qcurve.getUnchecked(k+1);
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
    
    /*
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
    */
    /*
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
    */
    
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
  pcurve.clear();
  times.clear();
  

  // first elements are 0
  double sumtime = 0.;
  pcurve.add(nullP);
  times.add(sumtime);
  for (int k=1; k<nPoints->intValue(); k++) // nPoints-1 iterations
  {
    if (k==0)
      continue;
    
    //cout << "k = " << k << endl;
    
    // handle time
    sumtime += opt_deltaT.getUnchecked(k-1);
    times.add(sumtime);
    
    // handle momentum, mean between current and next p
    if (k==nPoints->intValue()-1) // force last momentum vec to be 0
      pcurve.add(nullP);
    else
    {
      StateVec meanP;
      for (int m=0; m<opt_momentum.getUnchecked(k).size(); m++)
      {
        double pm = 0.5*(opt_momentum.getUnchecked(k-1).getUnchecked(m) + opt_momentum.getUnchecked(k).getUnchecked(m));
        meanP.add(pm);
      }
      pcurve.add(meanP);
    }
  }
  
  
  // TODO
  // smooth pcurve
  
  /*
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
  */
/*
  cout << "--- pcurve ---" << endl;
  for (auto & ppoint : pcurve)
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
*/

  jassert(pcurve.size() == qcurve.size());
  jassert(times.size() == qcurve.size());
  
  
  // Return optimization results
  LiftTrajectoryOptResults output;
  output.opt_deltaT = opt_deltaT;
  output.opt_momentum = opt_momentum;
  
  if (debug)
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
  cout << "qI : ";
  for (auto & qi : qI)
    cout << qi <<" ";
  cout << endl;
  for (auto & qf : qF)
    cout << qf << " ";
  cout << endl;
  
  
  jassert(qI.size() == simul->entities.size());
  jassert(qF.size() == simul->entities.size());
  
  // init with straight line between qI and qF
  qcurve.clear();
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
    qcurve.add(vec);
  }
  
  // init sample rate
  length_qcurve = curveLength(qcurve);
  if (length_qcurve>0.)
    sampleRate = (double) nPoints->intValue() / length_qcurve;
  else
  {
    LOGWARNING("qcurve has null length !!");
    sampleRate = 1000.;
  }
  /*
  // debugging
  cout << "curve size after init : " << qcurve.size() << ". nPoints = " << nPoints->intValue() << endl;
  cout << "points are : " << endl;
  int c=-1;
  for (auto & q : qcurve)
  {
    c++;
    cout << "point #" << c << "   : ";
    for (auto & qi : q)
      cout << qi << " ";
    cout << endl;
  }
  */
  
}

void NEP::filterConcentrationTrajectory()
{
  cout << "filtering concentration curve" << endl;
  // filter the gradient
  //filter.setCutoffFrequency(cutoffFreq->floatValue());
  //filter.prepare(sampleRate, simul->entities.size());
  filter.setSamplingRate(sampleRate);
  filter.setCutoffFrequency(cutoffFreq->floatValue());
  filter.process(qcurve);
}


void NEP::updateDescentParams()
{
  cout << "updating descent params" << endl;
  cutoffFreq->setValue(cutoffFreq->floatValue() + 10.);
  stepDescent = 1.;
}


bool NEP::descentShouldUpdateParams(double diffAction)
{
  return ((diffAction<action_threshold->floatValue() || stepDescent<stepDescentThreshold));
}

bool NEP::descentShouldContinue(int step)
{
  return (step<=Niterations->intValue() || cutoffFreq->floatValue()<maxcutoffFreq->floatValue());
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
  historyFile << endl;
  cout << "action descent size :" << actionDescent.size() << endl;
  cout << "trajDescent descent size :" << trajDescent.size() << endl;
  cout << "grad Descent size :" << dAdqDescent.size() << endl;
  jassert(actionDescent.size() == trajDescent.size());
  jassert(actionDescent.size() == dAdqDescent.size());
  
  for (int iter=0; iter<actionDescent.size(); iter++)
  {
    for (int point=0; point<trajDescent.getUnchecked(iter).size(); point++)
    {
      historyFile << iter << "," << actionDescent.getUnchecked(iter) << "," << point;
      PhaseSpaceVec trajpq = trajDescent.getUnchecked(iter).getUnchecked(point);
      StateVec dAdq = dAdqDescent.getUnchecked(iter).getUnchecked(point);
      //cout << "trajectory size : " << trajpq.size() << endl;
      for (int m=0; m<trajpq.size()/2; m++)
        historyFile << "," << trajpq.getUnchecked(m);
      for (int m=trajpq.size()/2; m<trajpq.size(); m++)
        historyFile << "," << trajpq.getUnchecked(m);
      for (int m=0; m<dAdq.size(); m++)
        historyFile << "," << dAdq.getUnchecked(m);
      historyFile << endl;
    } // end loop over points in current iteration
    //historyFile << endl;
  } // end loop over iterations
  
}





void NEP::updateOptimalConcentrationCurve_old(const Array<StateVec> popt, const Array<double> deltaTopt)
{
  jassert(popt.size() == nPoints->intValue()-1);
  jassert(deltaTopt.size() == nPoints->intValue()-1);
  //jassert(purve.size() == nPoints->intValue());
  /*
  cout << "--- updateOptimalConcentrationCurve() ---" << endl;
  cout << "popt = ";
  for (auto & psv :popt)
  {
    for (auto & p : psv)
      cout << p << " ";
    cout << endl;
  }
  cout << "dtopt = ";
  for (auto & dt : deltaTopt)
    cout << dt << " ";
  cout << endl;
  */
  
  // for each trajectory point, calculate action gradient w.r.t q
  Array<Array<double>> dAdq;
  
  // first and last points of the trajectory remain unchanged, so init null vector
  Array<double> nullVec;
  nullVec.insertMultiple(0, 0., simul->entities.size());
    
  
  for (int k=0; k<nPoints->intValue(); k++) // descend point k of optimized trajectory
  {
    // first and last points remain unchanged
    if (k==0 || k==nPoints->intValue()-1)
    {
      dAdq.add(nullVec);
      continue;
    }
    //cout << "point " << k << endl;
    
    StateVec dAdqk(nullVec);
    StateVec gradqH = evalHamiltonianGradientWithQ(qcurve.getUnchecked(k), pcurve.getUnchecked(k));
    /*cout << "dH/dq = ";
    for (auto & g : gradqH)
      cout << g << " ";
    cout << endl;*/
    double deltatk = 0.5*(deltaTopt.getUnchecked(k-1) + deltaTopt.getUnchecked(k));
    //cout << "dtmean = " << deltatk << endl;
    
    // delta A / delta q = - ( dp/dt + dH/dq)
    for (int m=0; m<popt.getUnchecked(k-1).size(); m++)
    {
      // calculate dp / dt at coordinate m
      double dqm = -1.*(popt.getUnchecked(k).getUnchecked(m) - popt.getUnchecked(k-1).getUnchecked(m)) / deltatk;
      //cout << "\tdp/dt_" << m << " = " << -1.*dqm << endl;
      dqm -= gradqH.getUnchecked(m);
      dAdqk.setUnchecked(m, dqm);
    }
    
    dAdq.add(dAdqk);
    /*
    cout << "dAdq #" << k << " = " << endl;
    for (auto & qm : dAdqk)
      cout << qm << " ";
    cout << endl;
    */
  }
  
  
  // filter the gradient
  //filter.setCutoffFrequency(cutoffFreq->floatValue());
  //filter.prepare(sampleRate, simul->entities.size());
  filter.setSamplingRate(sampleRate);
  filter.setCutoffFrequency(cutoffFreq->floatValue());
  filter.process(dAdq);
  
  
  stepDescent = backTrackingMethodForStepSize(qcurve, dAdq);
  //double step = backTrackingMethodForStepSize(qcurve, dAdq);
  //double step = 1.;
  //cout << "step for descent = " << step << endl;
  
  
  // update concentration curve
  for (int k=0; k<nPoints->intValue(); k++)
  {
    // update curve point k component wise
    StateVec newqk;
    for (int m=0; m<qcurve.getUnchecked(k).size(); m++)
    {
      //double qnew = qcurve.getUnchecked(k).getUnchecked(m) - step * deltaq.getUnchecked(k).getUnchecked(m);
      //qcurve.setUnchecked(int indexToChange, <#ParameterType newValue#>)
      newqk.add( qcurve.getUnchecked(k).getUnchecked(m) - stepDescent * dAdq.getUnchecked(k).getUnchecked(m) );
      //newqk.add( qcurve.getUnchecked(k).getUnchecked(m) + step * dAdq.getUnchecked(k).getUnchecked(m) );
    }
    qcurve.setUnchecked(k, newqk);
    //qcurve.add(newqk);
  }
  length_qcurve = curveLength(qcurve);
  if (length_qcurve>0.)
    sampleRate = (double) nPoints->intValue() / length_qcurve;
  jassert(qcurve.size() == nPoints->intValue());
  
}




// update concentration curve as q^I = q^(I-1) - stepDescent * dAdq_filtered
void NEP::updateOptimalConcentrationCurve()
{

  for (int k=0; k<nPoints->intValue(); k++)
  {
    // update curve point k component wise
    StateVec newqk;
    for (int m=0; m<qcurve.getUnchecked(k).size(); m++)
    {
      newqk.add( qcurve.getUnchecked(k).getUnchecked(m) - stepDescent * dAdq_filt.getUnchecked(k).getUnchecked(m) );
    }
    qcurve.setUnchecked(k, newqk);
    //qcurve.add(newqk);
  }
  length_qcurve = curveLength(qcurve);
  if (length_qcurve>0.)
    sampleRate = (double) nPoints->intValue() / length_qcurve;
  jassert(qcurve.size() == nPoints->intValue());
  
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
   // cout << "\tdelta Ti = " << deltaTi << endl;
    // integrad at i
    double integrand = -0.5 * (hamilt.getUnchecked(i) + hamilt.getUnchecked(i+1)) * deltaTi;
   // cout << "\t-mean H x deltaT_"<< i << " = " << integrand << endl;
    jassert(pc.getUnchecked(i).size() == pc.getUnchecked(i+1).size()); // safety check
    jassert(qc.getUnchecked(i).size() == qc.getUnchecked(i+1).size());
    for (int m=0; m<qc.getUnchecked(i).size(); m++)
    {
      double sp = 0.5 * (pc.getUnchecked(i).getUnchecked(m) + pc.getUnchecked(i+1).getUnchecked(m)) * (qc.getUnchecked(i+1).getUnchecked(m)-qc.getUnchecked(i).getUnchecked(m));
      integrand += sp;
      //cout << "\t(sp)_" << m << " = 1/2 * (" << pc.getUnchecked(i+1).getUnchecked(m) << "+" << pc.getUnchecked(i).getUnchecked(m);
      //cout << " * (" << qc.getUnchecked(i+1).getUnchecked(m) << "-" << qc.getUnchecked(i).getUnchecked(m) << ")" << " = " << sp << endl;
    }
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


double NEP::backTrackingMethodForStepSize(const Curve& qc, const Curve& dAdq)
{
  // init step with large value #para ?
  double step = 1.;
  int timeout = 30; // (2/3)^30 < 1e-5, will trigger the loop to break
  
  double currentaction = calculateAction(qc, pcurve, times);
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
  for (auto & pm : pcurve.getUnchecked(nPoints->intValue()/2))
    cout << pm << " ";
  cout << endl;
  cout << "t = " << times.getUnchecked(nPoints->intValue()/2) << endl;
  */
  
  StateVec nullvec;
  nullvec.insertMultiple(0, 0., simul->entities.size());
 
  for (int iter=0; iter<timeout; iter++)
  {
    if (step<1e-5)
      break;
    
    Curve newcurve;
    for (int point=0; point<nPoints->intValue(); point++)
    {
      if (point==0 || point == nPoints->intValue()-1)
      {
        newcurve.add(qc.getUnchecked(point)); // leave point unchanged
        continue;
      }
      StateVec newqk;
      jassert(qc.getUnchecked(point).size()==dAdq.getUnchecked(point).size());
      
      //double norm=0.;
      //for (auto d : deltaqc.getUnchecked(point))
      //  norm += d*d;
      //cout << "deltaqc norm : "  << norm << endl;
      
      // q(point+1) = q(point) + dq
      // and dq = -step
      for (int m=0; m<qc.getUnchecked(point).size(); m++)
      {
        double newval = qc.getUnchecked(point).getUnchecked(m) - step*dAdq.getUnchecked(point).getUnchecked(m);
        //double newval = qc.getUnchecked(point).getUnchecked(m) + step*dAdq.getUnchecked(point).getUnchecked(m);
        // #HERE I'm puzzled, from calculations the correct sign should be '-', but the loop does not converge unless I
        // use the opposite sign...?
        newqk.add(newval);
      }
      newcurve.add(newqk);
    }
    
    /* debugging
    cout << "new q = ";
    for (auto & qm : newcurve.getUnchecked(nPoints->intValue()/2))
      cout << qm << " ";
    cout << endl;
    cout << "new p = " ;
    for (auto & pm : pcurve.getUnchecked(nPoints->intValue()/2))
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
    double newact = calculateAction(newcurve, pcurve, times);
    cout << "iter = " << iter << ". step = " << step << ". new action = " << newact << " vs current action = " << currentaction << endl;
    if (newact>=currentaction)
    {
      cout << "decreasing step" << endl;
      step *= 2./3.; // hardcoded (2/3)^20 = 5e-6, should be enough
      //cout << "new step val = " << step << endl;
    }
    else
    {
      //cout << "exiting loop" << endl;
      break;
    }
  }
  //cout << "will return step = " << step << endl;
  
  //LOGWARNING("backtracking algorithm did not converge to pick a descent step size. Returning 1e-6 as default value. Caution.");
  return step;
}




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
  // lift it to full (q ; p) space
  liftCurveToTrajectory();
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
  if (qcurve.size() > 1 && pcurve.size() > 1)
  {
    q_init = qcurve.getUnchecked(1);
    p_init = pcurve.getUnchecked(1);
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



void NEP::debugFiltering()
{
  state = Idle;
  cout << "debugFiltering" << endl;
  //data
  cout << "##" << endl;
  Trajectory traj;
  cout << "#0" << endl;
  traj.add({1.00115,1.00115});
  cout << "#1" << endl;
  traj.add({1.00662,1.00163});
  traj.add({1.01103,1.00215});
  traj.add({1.01386,1.00272});
  traj.add({1.01518,1.00332});
  traj.add({1.01537,1.00389});
  traj.add({1.01493,1.00441});
  traj.add({1.01431,1.00484});
   //iteration,action,point,q_X1,q_X2,p_X1,p_X2,dAdq_X1,dAdq_X2
  traj.add({1.01388,1.00517});
  traj.add({1.01385,1.00541});
  traj.add({1.01432,1.00557});
traj.add({1.01527,1.0057});
traj.add({1.01663,1.00583});
traj.add({1.0183,1.00597});
traj.add({1.02019,1.00616});
traj.add({1.0222,1.0064});
traj.add({1.02428,1.0067});
  traj.add({1.02639,1.00704});
  traj.add({1.02852,1.00743});
  traj.add({1.03068,1.00786});
  traj.add({1.03289,1.00831});
  traj.add({1.03518,1.00877});
  traj.add({1.03756,1.00924});
  traj.add({1.04007,1.00971});
  traj.add({1.04272,1.01018});
  cout << "#2" << endl;
  traj.add({1.04554,1.01065});
  traj.add({1.04853,1.01113});
  traj.add({1.05171,1.0116});
  traj.add({1.05508,1.01209});
  traj.add({1.05866,1.01259});
  traj.add({1.06243,1.01309});
  traj.add({1.06642,1.01361});
  traj.add({1.07063,1.01414});
  traj.add({1.07506,1.01469});
  traj.add({1.07972,1.01525});
  traj.add({1.08461,1.01582});
  traj.add({1.08975,1.0164});
  traj.add({1.09513,1.017});
  traj.add({1.10077,1.01761});
  traj.add({1.10666,1.01823});
  traj.add({1.11281,1.01886});
  traj.add({1.11923,1.01949});
  traj.add({1.1259,1.02014});
  traj.add({1.13285,1.02079});
  traj.add({1.14006,1.02145});
  traj.add({1.14753,1.02211});
  traj.add({1.15526,1.02278});
  traj.add({1.16324,1.02346});
  traj.add({1.17147,1.02413});
  traj.add({1.17993,1.02482});
  traj.add({1.18863,1.0255});
  traj.add({1.19754,1.02619});
  traj.add({1.20666,1.02687});
  traj.add({1.21597,1.02756});
  traj.add({1.22545,1.02825});
  traj.add({1.2351,1.02893});
  traj.add({1.2449,1.02962});
  traj.add({1.25482,1.0303});
  traj.add({1.26486,1.03098});
  traj.add({1.275,1.03165});
           traj.add({1.28521,1.03233});
      traj.add({1.29548,1.03299});
  traj.add({1.3058,1.03365});
  traj.add({1.31615,1.03431});
  traj.add({1.32651,1.03496});
  traj.add({1.33686,1.0356});
  traj.add({1.34719,1.03624});
  traj.add({1.3575,1.03687});
  traj.add({1.36776,1.0375});
  traj.add({1.37796,1.03812});
  traj.add({1.38809,1.03873});
  traj.add({1.39815,1.03933});
  traj.add({1.40813,1.03993});
  traj.add({1.41801,1.04052});
  traj.add({1.42779,1.0411});
  traj.add({1.43747,1.04167});
  traj.add({1.44703,1.04224});
  traj.add({1.45648,1.0428});
  traj.add({1.46582,1.0433});
  traj.add({1.47504,1.04391});
  traj.add({1.48413,1.04445});
  traj.add({1.4931,1.04498});
  traj.add({1.50195,1.04551});
  traj.add({1.51068,1.04603});
  traj.add({1.51928,1.04655});
  traj.add({1.52776,1.0470});
  traj.add({1.53612,1.04756});
  traj.add({1.54436,1.04806});
  traj.add({1.55249,1.04856});
  traj.add({1.56049,1.04905});
  traj.add({1.56839,1.04953});
  traj.add({1.57617,1.05001});
  traj.add({1.58384,1.05048});
  traj.add({1.5914,1.05095});
  traj.add({1.59886,1.05142});
  traj.add({1.60621,1.05188});
  traj.add({1.61347,1.05234});
  traj.add({1.62063,1.05279});
  traj.add({1.62769,1.05324});
               traj.add({1.63466,1.05368});
  traj.add({1.64155,1.05413});
  traj.add({1.64834,1.05456});
  traj.add({1.65505,1.055});
               traj.add({1.66168,1.05543});
               traj.add({1.66823,1.05586});
               traj.add({1.6747,1.05629});
               traj.add({1.6811,1.05671});
               traj.add({1.68743,1.05713});
               traj.add({1.69368,1.05755});
               traj.add({1.69987,1.05797});
               traj.add({1.706,1.05838});
                 traj.add({1.71206,1.05879});
                          traj.add({1.71806,1.0592});
                          traj.add({1.724,1.05961});
                          traj.add({1.72988,1.06001});
                          traj.add({1.73571,1.06041});
                          traj.add({1.74148,1.06082});
                          traj.add({1.74721,1.06122});
                          traj.add({1.75288,1.06161});
                          traj.add({1.75851,1.06201});
                          traj.add({1.76409,1.06241});
                          traj.add({1.76963,1.0628});
                          traj.add({1.77512,1.06319});
                          traj.add({1.78058,1.06358});
                          traj.add({1.78599,1.06397});
                          traj.add({1.79137,1.06436});
                          traj.add({1.79671,1.06475});
                          traj.add({1.80201,1.06514});
                          traj.add({1.80728,1.06552});
                          traj.add({1.81252,1.06591});
                          traj.add({1.81773,1.06629});
                          traj.add({1.82291,1.06668});
                          traj.add({1.82806,1.06706});
                          traj.add({1.83318,1.06744});
                          traj.add({1.83828,1.06783});
                          traj.add({1.84335,1.06821});
                          traj.add({1.8484,1.06859});
                          traj.add({1.85343,1.06897});
                          traj.add({1.85844,1.06935});
                          traj.add({1.86342,1.06973});
                          traj.add({1.86839,1.07011});
                          traj.add({1.87334,1.07049});
                          traj.add({1.87827,1.07087});
                          traj.add({1.88318,1.07125});
                          traj.add({1.88808,1.07163});
                          traj.add({1.89297,1.07201});
                          traj.add({1.89784,1.07239});
                          traj.add({1.9027,1.07277});
                          traj.add({1.90754,1.07315});
                          traj.add({1.91238,1.07354});
                          traj.add({1.91721,1.07392});
                          traj.add({1.92202,1.0743});
                          traj.add({1.92683,1.07468});
                          traj.add({1.93163,1.07506});
                          traj.add({1.93643,1.07544});
                          traj.add({1.94121,1.07582});
                          traj.add({1.946,1.07621});
                          traj.add({1.95078,1.07659});
                          traj.add({1.95555,1.07698});
                          traj.add({1.96032,1.07736});
                          traj.add({1.96509,1.07774});
                          traj.add({1.96986,1.07813});
                          traj.add({1.97462,1.07852});
                          traj.add({1.97939,1.0789});
                          traj.add({1.98415,1.07929});
                          traj.add({1.98892,1.07968});
                          traj.add({1.99368,1.08007});
                          traj.add({1.99845,1.08046});
                          traj.add({2.00323,1.08085});
                          traj.add({2.008,1.08124});
                          traj.add({2.01278,1.08164});
                          traj.add({2.01756,1.08203});
                          traj.add({2.02235,1.08242});
                          traj.add({2.02714,1.08282});
                          traj.add({2.03194,1.08322});
                          traj.add({2.03675,1.08361});
                          traj.add({2.04156,1.08401});
                          traj.add({2.04638,1.08441});
                          traj.add({2.05121,1.08481});
                          traj.add({2.05604,1.08522});
                          traj.add({2.06089,1.08562});
                          traj.add({2.06574,1.08602});
                          traj.add({2.07061,1.08643});
                          traj.add({2.07548,1.08684});
                          traj.add({2.08037,1.08725});
                          traj.add({2.08527,1.08766});
                          traj.add({2.09018,1.08807});
                          traj.add({2.0951,1.08848});
                          traj.add({2.10003,1.08889});
                          traj.add({2.10498,1.08931});
             traj.add({2.10994,1.08972});
             traj.add({2.11491,1.09014});
             traj.add({2.1199,1.09056});
             traj.add({2.1249,1.09098});
             traj.add({2.12992,1.0914});
             traj.add({2.13495,1.0918});
             traj.add({2.14,1.09225});
             traj.add({2.14507,1.09268});
             traj.add({2.15015,1.09311});
             traj.add({2.15525,1.09354});
  
  cout << "flag A0" << endl;
   
  Trajectory trajfilter = traj;
  
  float sr = (float) curveLength(traj) / float(traj.size());
  filter.setCutoffFrequency(cutoffFreq->floatValue());
  //filter.prepare(sr, simul->entities.size());
  filter.setSamplingRate(sr);
  filter.setCutoffFrequency(cutoffFreq->floatValue());
  filter.process(trajfilter);
  
  cout << "flag A" << endl;
  
  // open output file
  String filename = "debug-filtering.csv";
  ofstream historyFile;
  historyFile.open(filename.toStdString(), ofstream::out | ofstream::trunc);
  
  historyFile << "point";
  for (auto & ent : simul->entities)
    historyFile << ",q_" << ent->name << ",qfilt_" << ent->name;
  historyFile << endl;

  cout << "flag B" << endl;
  cout << traj.size() << " " << trajfilter.size() << endl;

    for (int point=0; point<traj.size(); point++)
    {
      historyFile << point;
      StateVec q = traj.getUnchecked(point);
      StateVec qfilt = trajfilter.getUnchecked(point);
      
      for (int m=0; m<q.size(); m++)
      {
        historyFile << "," << q.getUnchecked(m) << "," << qfilt.getUnchecked(m);
      }
      historyFile << endl;
    } // end loop over points in current iteration
    //historyFile << endl;
  
  cout << "END debugFiltering" << endl;
  state = Idle;
  
}
