//  NEP.cpp
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//

#include "NEP.h"

juce_ImplementSingleton(NEP);


struct EncapsVarForNLOpt {
  const Array<double>* qcenter; // current concentration point
  const Array<double>* deltaq; // current concentration point
  Array<double>* p; // p variable to pass to t optimisation
  NEP * nep; // nep class for hamiltonian class
  double t_opt; // t variable that optimizes the lagrangian
  //Array<double> p_opt; // t variable that optimizes the lagrangian
};


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
  
  /*
  cout << "check p "<< endl;
  for (auto & pi : *ev->p)
    cout << pi << " ";
  cout << endl;
  */
  
  // ----- Step 1 : minimize hamiltonian w.r.t to t at fixed p -----
  //nlopt::opt opt_t(nlopt::LD_LBFGS, 1);  // t is scalar variable
  //nlopt::opt opt_t(nlopt::LN_COBYLA, 1);  // method without gradient
  

  // lower and upper bounds
  //vector<double> lowerbound_t(1, 0.0);
  //vector<double> upperbound_t(1, 100.0);
  //opt_t.set_lower_bounds(lowerbound_t);
  //opt_t.set_upper_bounds(upperbound_t);
  

  // define function to minimize
  //opt_t.set_min_objective(objective_min_t, f_data);
  //opt_t.set_xtol_rel(1e-6);

  //std::vector<double> t(1, 0.0);
  //double minf;

  //nlopt::result result = opt_t.optimize(t, minf);
  
  // stock optimize t value
  //ev->t_opt = t[0];
  
  // convert grad to vector
  //vector<double> gradvec(grad, grad + n);

  // if we want the gradient w.r.t p :
  //if (!gradvec.empty())

  /*
  if (grad != nullptr)
  {

    StateVec gradH = ev->nep->evalHamiltonianGradientWithP(*ev->qcenter, *ev->p);
    //Array<double> actualgrad;
    //jassert(gradH.size() == ev->deltaq->size());
    cout << "gradientP : ";
    for (int k=0; k<gradH.size(); k++)
    {
      grad[k] = gradH.getUnchecked(k);
      cout << grad[k] << " ";
      //actualgrad.add( ev->deltaq->getUnchecked(k) - gradH.getUnchecked(k)*t[0] );
    }
    cout << endl;
    //for (unsigned i = 0; i < gradH.size(); ++i)
     //   grad[i] = actualgrad[i];
  }
  */

    
  // return  opposite of min found -----
  //return -minf; // car on veut max_p => -min_t
 }
 



NEP::NEP() : ControllableContainer("NEP"), Thread("NEP"), simul(Simulation::getInstance())
{
  
  //rm = new RunManager();
  //ShapeShifterFactory::getInstance()->defs.add(new ShapeShifterDefinition("RunManager", &RunManagerUI::create));

  
  showWarningInUI = true;
  saveAndLoadRecursiveData = true;
  includeInRecursiveSave = true;
  
  // set this class as simulation listener
  simul->addAsyncSimulationListener(this);
  simul->addAsyncContainerListener(this);
  
  // affect satID to entities
  simul->affectSATIds();
  
  startDescent = addTrigger("Start Descent", "Start action functionnal descent algorithm");

  // enum parameters = steady states
  sst_stable = addEnumParameter("Stable steady state", "Choose stable fixed point to start the NEP algorithm from");
  sst_saddle = addEnumParameter("Unstable steady state", "Choose unstable fixed point to start the NEP algorithm from");
  
  
  // set options
  updateSteadyStateList();
  /*
  sst_stable->clearOptions();
  sst_saddle->clearOptions();
  //for (int k=0; k<Simulation::getInstance()->steadyStatesList->arraySteadyStates.size(); k++)
  for (int k=0; k<simul->steadyStatesList->arraySteadyStates.size(); k++)
  {
    //SteadyState sst = Simulation::getInstance()->steadyStatesList->arraySteadyStates.getUnchecked(k);
    SteadyState sst = simul->steadyStatesList->arraySteadyStates.getUnchecked(k);
    if (sst.isBorder)
      continue;
    sst_stable->addOption(String(k), k);
    sst_saddle->addOption(String(k), k);
  }
  */

  
}





NEP::~NEP()
{
  simul->removeAsyncSimulationListener(this);
  simul->removeAsyncContainerListener(this);
}


void NEP::updateSteadyStateList()
{
  // set options
  sst_stable->clearOptions();
  sst_saddle->clearOptions();
  //for (int k=0; k<Simulation::getInstance()->steadyStatesList->arraySteadyStates.size(); k++)
  for (int k=0; k<simul->steadyStatesList->arraySteadyStates.size(); k++)
  {
    SteadyState sst = simul->steadyStatesList->arraySteadyStates.getUnchecked(k);
    if (sst.isBorder)
      continue;
    /*
     TODO : options to add should depend on stability of steady states
     */
    sst_stable->addOption(String(k), k);
    sst_saddle->addOption(String(k), k);
  }
  
}


void NEP::onContainerParameterChanged(Parameter *p)
{
/*
  if (p == nRuns)
  {
    
  }
*/
}


void NEP::onContainerTriggerTriggered(Trigger* t)
{
  if (t == startDescent)
  {
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
  /*
  cout << "--- hamiltonian check --- " << endl;
  for (int k=0; k<vecH.size(); k++)
  {
    cout << "H" << k << " = " << vecH.getUnchecked(k) << endl;
  }
  cout << "Htot = " << H << endl;
  */
  
  return H;
}




StateVec NEP::evalHamiltonianGradientWithP(const StateVec q, const StateVec p)
{
  // init output
  StateVec gradpH(0., q.size());
  
  
  // loop over reactions
  for (auto & reaction : Simulation::getInstance()->reactions)
  {
    // forward reaction
    double forward = reaction->assocRate;
    double sp1 = 0.;
    double pow1 = 1.;
    StateVec prevec1(0., gradpH.size());
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
    
    
    // backward contribution
    double backward = reaction->dissocRate;
    double sp2 = 0.;
    double pow2 = 1.;
    StateVec prevec2(0., gradpH.size());
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
    
    // update output array with forward reaction
    for (int k=0; k<gradpH.size(); k++)
    {
      gradpH.setUnchecked(k, prevec1.getUnchecked(k)*forward + prevec2.getUnchecked(k)*backward );
    }
  } // end loop over reactions
  
  return gradpH;
}




StateVec NEP::evalHamiltonianGradientWithQ(const StateVec q, const StateVec p)
{
  jassert(q.size() == p.size());
  jassert(q.size() == Simulation::getInstance()->entities.size());
  
  // output gradient vector
  StateVec gradqH(q.size(), 0.);
  
  // loop over reactions
  for (auto & reaction : Simulation::getInstance()->reactions)
  {
    // set stoechiometric vector of reactants and product sides
    StateVec yreactants(q.size(), 0.);
    StateVec yproducts(q.size(), 0.);
    // keep track of polynom involved in MAK
    map<int, int> polyforward; // <int, int> --> <idSAT, power>
    map<int, int> polybackward; //
    for (auto & r: reaction->reactants)
    {
      yreactants.setUnchecked(r->idSAT, yreactants.getUnchecked(r->idSAT) - 1 );
      polyforward[r->idSAT]++;
    }
    for (auto & p: reaction->products)
    {
      yproducts.setUnchecked(p->idSAT, yproducts.getUnchecked(p->idSAT) + 1 );
      polybackward[p->idSAT]++;
    }
    
    // forward reaction
    double forward_prefactor = reaction->assocRate;
    double spfor = 0.;
    for (int m=0; m<p.size(); m++)
      spfor += (yproducts.getUnchecked(m)-yreactants.getUnchecked(m)) * p.getUnchecked(m);
    forward_prefactor *= (exp(spfor) - 1.);
    // now derivative of polynom in concentration
    for (auto & [id, exponent] : polyforward)
    {
      double monom = exponent * pow(q.getUnchecked(id), exponent-1.);
      for (auto & [id2, exponent2] : polyforward)
      {
        if (id2==id)
          continue;
        monom *= pow(q.getUnchecked(id2), exponent2);
      }
      gradqH.setUnchecked(id, gradqH.getUnchecked(id) + forward_prefactor*monom);
    }
    
    // backward reaction
    double backward_prefactor = reaction->dissocRate;
    double spback = 0.;
    for (int m=0; m<p.size(); m++)
      spback += (yreactants.getUnchecked(m)-yproducts.getUnchecked(m)) * p.getUnchecked(m);
    backward_prefactor *= (exp(spback) - 1.);
    // now derivative of polynom in concentration
    for (auto & [id, exponent] : polybackward)
    {
      double monom = exponent * pow(q.getUnchecked(id), exponent-1.);
      for (auto & [id2, exponent2] : polybackward)
      {
        if (id2==id)
          continue;
        monom *= pow(q.getUnchecked(id2), exponent2);
      }
      gradqH.setUnchecked(id, gradqH.getUnchecked(id) + backward_prefactor*monom);
    }
    
  } // end reaction loop

  return gradqH;
  
}





// start thread
void NEP::run()
{
  simul->affectSATIds();
  
  
  Array<double> qcenter = { 0.5*(1.00115+1.57702) , 0.5*(1.00115+1.04734) };
  Array<double> deltaq = { (-1.00115+1.57702) , (-1.00115+1.04734) };
  
  cout << "init concentration curve" << endl;
  // init concentration trajectory
  initConcentrationCurve();
  
  int count = -1;
  while (count < maxIter && !threadShouldExit())
  {
    count++;
    cout << "iteration #" << count << endl;
    // lift current trajectory to full (q ; p; t) space
    // this function updates global variables pcurve and times
    cout << "lifting trajectory" << endl;
    LiftTrajectoryOptResults liftoptres = liftCurveToTrajectory();
    
    // keep track of trajectory update in (q ; p) space
    Trajectory newtraj;
    for (int point=0; point<nPoints; point++)
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
    
    cout << "updating action" << endl;
    calculateNewActionValue();
    cout << "action = " << action << endl;
    //if (action < action_threshold)
    //  break;
    
    cout << "updating concentration curve" << endl;
    // now update the concentration trajectory with functionnal gradient descent
    // this function update global variable qcurve
    updateOptimalConcentrationCurve(liftoptres.opt_momentum, liftoptres.opt_deltaT);
    
    // I could call at this stage a NEPEvent to display real time algorithm progress in the NEPUI window
    // that would be really badass, but not a priority
    
    
  } // end while
  
  cout << actionDescent.size() << " --- " << trajDescent.size() << endl;
  
  // save descent algorithm results into a file
  cout << "writing to file" << endl;
  writeDescentToFile();
  
  
  
}




LiftTrajectoryOptResults NEP::liftCurveToTrajectory()
{
  int nent = Simulation::getInstance()->entities.size();
  //nlopt::opt opt(nlopt::LD_LBFGS, nent);  // momentum is nentities dimensionnal
  //nlopt::opt opt(nlopt::LN_COBYLA, nent);  // momentum is nentities dimensionnal
  nlopt::opt opt(nlopt::GN_DIRECT_L, nent);  // no gradient
  
  //int nPoints = qcurve.size(); //

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
  for (int k=0; k<nPoints-1; k++) // n - 1 iterations
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
    cout << "--- optima found ---" << endl;
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
  jassert(opt_deltaT.size() == nPoints-1);
  
  // Build full trajectory in (q ; p) space from optima found previously
  //Array<double> tTraj;
  //Curve pTraj;
  pcurve.clear();
  times.clear();

  // first elements are 0
  double sumtime = 0.;
  pcurve.add(nullP);
  times.add(sumtime);
  for (int k=1; k<nPoints; k++) // nPoints-1 iterations
  {
    if (k==0)
      continue;
    
    // handle time
    sumtime += opt_deltaT.getUnchecked(k-1);
    times.add(sumtime);
    
    // handle momentum, mean between current and next p
    if (k==nPoints-1) // force last momentum vec to be 0
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
  /*
  cout << "--- pcurve ---" << endl;
  for (auto & ppoint : pcurve)
  {
    for (auto & pm : ppoint)
      cout << pm << " ";
    cout << endl;
  }
*/
  jassert(pcurve.size() == qcurve.size());
  jassert(times.size() == qcurve.size());
  
  
  // Return optimization results
  LiftTrajectoryOptResults output;
  output.opt_deltaT = opt_deltaT;
  output.opt_momentum = opt_momentum;
  
  return output;
  
}




void NEP::initConcentrationCurve()
{
  // read init and final curve points from enum parameters
  int sstI = sst_stable->intValue();
  int sstF = sst_saddle->intValue();
  
  StateVec qI(simul->entities.size(), 0.);
  StateVec qF(simul->entities.size(), 0.);
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
  double NN = (double) nPoints;
  jassert(nPoints>0);
  for (int point=0; point<nPoints; point++)
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
  /*
  // debugging
  cout << "curve size after init : " << qcurve.size() << ". nPoints = " << nPoints << endl;
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
  historyFile << endl;
  cout << "action descent size :" << actionDescent.size() << endl;
  cout << "trajDescent descent size :" << trajDescent.size() << endl;
  jassert(actionDescent.size() == trajDescent.size()); // HERE
  
  for (int iter=0; iter<actionDescent.size(); iter++)
  {
    for (int point=0; point<trajDescent.getUnchecked(iter).size(); point++)
    {
      historyFile << iter << "," << actionDescent.getUnchecked(iter) << "," << point;
      PhaseSpaceVec trajpq = trajDescent.getUnchecked(iter).getUnchecked(point);
      //cout << "trajectory size : " << trajpq.size() << endl;
      for (int m=0; m<trajpq.size()/2; m++)
        historyFile << "," << trajpq.getUnchecked(m);
      for (int m=trajpq.size()/2; m<trajpq.size(); m++)
        historyFile << "," << trajpq.getUnchecked(m);
      historyFile << endl;
    } // end loop over points in current iteration
    //historyFile << endl;
  } // end loop over iterations
  
}





void NEP::updateOptimalConcentrationCurve(const Array<StateVec> popt, const Array<double> deltaTopt)
{
  jassert(popt.size() == nPoints-1);
  jassert(deltaTopt.size() == nPoints-1);
  //jassert(purve.size() == nPoints);
  
  // hardcode step descent for now
  float step = 0.01; // #para
  
  // for each trajectory point, assign a gradient vector in the q space
  Array<Array<double>> deltaq;
  
  // first and last points of the trajectory remain unchanged, so init null vector
  Array<double> nullVec(Simulation::getInstance()->entities.size(), 0.);
  
  //
  for (int k=0; k<nPoints; k++) // descend point k of optimized trajectory
  {
    if (k==0 || k==nPoints-1) // first and last points remain unchanged
      continue;
      //deltaq.add(nullVec);
    
    //
    StateVec deltaqk(nullVec);
    StateVec gradqH = evalHamiltonianGradientWithQ(qcurve.getUnchecked(k), pcurve.getUnchecked(k));
    double deltatk = 0.5*(deltaTopt.getUnchecked(k-1) + deltaTopt.getUnchecked(k));
    
    for (int m=0; m<popt.getUnchecked(k-1).size(); m++)
    {
      double dqm = (popt.getUnchecked(k).getUnchecked(m) - popt.getUnchecked(k).getUnchecked(m)) / deltatk;
      dqm += gradqH.getUnchecked(m);
      deltaqk.setUnchecked(m, dqm);
    }
    
    // update curve point k component wise
    StateVec newqk;
    for (int m=0; m<qcurve.getUnchecked(k).size(); m++)
    {
      newqk.add( qcurve.getUnchecked(k).getUnchecked(m) - step * deltaqk.getUnchecked(m) );
    }
    qcurve.setUnchecked(k, newqk);
  }
  
  jassert(qcurve.size() == nPoints);
  
}


void NEP::calculateNewActionValue()
{
  // check that pcurve, qcurve and tcurve have the same size
  jassert(qcurve.size() == pcurve.size());
  jassert(qcurve.size() == times.size());
    
  Array<double> hamilt;
  for (int i=0; i<qcurve.size(); i++)
  {
    hamilt.add(evalHamiltonian(qcurve.getUnchecked(i), pcurve.getUnchecked(i)));
  }
  
  // use trapezoidal rule to calculate action = integral(0, T, p dq/dt - H)
  double newaction = 0.;
  for (int i=0; i<qcurve.size()-1; i++)
  {
    double deltaTi = times.getUnchecked(i+1) - times.getUnchecked(i);
    
    // integrad at i
    double integrand = -0.5 * (hamilt.getUnchecked(i) + hamilt.getUnchecked(i+1));
    jassert(pcurve.getUnchecked(i).size() == pcurve.getUnchecked(i+1).size()); // safety check
    jassert(qcurve.getUnchecked(i).size() == qcurve.getUnchecked(i+1).size());
    for (int m=0; m<qcurve.getUnchecked(i).size(); m++)
    {
      integrand += 0.5 * (pcurve.getUnchecked(i).getUnchecked(m) + pcurve.getUnchecked(i+1).getUnchecked(m)) * (qcurve.getUnchecked(i+1).getUnchecked(m)-qcurve.getUnchecked(i).getUnchecked(m));
    }
    newaction += integrand * deltaTi;
  }
  
  // update action value
  action = newaction;
  // keep track of action history
  actionDescent.add(newaction);
  
  
}



void NEP::loadJSONData(var data, bool createIfNotThere)
{
  /*
  if (data.isVoid())
    return;
  
  if (!data.getDynamicObject()->hasProperty("runs"))
  {
    LOGWARNING("couldn't retrieve any run from json file");
    return;
  }
  
  // load runs
  auto arrayruns = data.getProperty("runs", juce::var());
  // retrieve runs
 // cout << "is array ? --> " << data.getProperty("runs", juce::var()).isArray() << endl;
  
  if (!data.getProperty("runs", juce::var()).isArray())
  {
    LOGWARNING(" Runs not stored as array in json file, will not init them");
    return;
  }
  
  
  // loop over stored runs
  for (auto & arun : *arrayruns.getArray())
  {
    if (!arun.getDynamicObject()->hasProperty("parameters"))
    {
      LOGWARNING(" No parameters in run.");
      return;
    }
    
    Run * newrun = new Run(arun);
    addRun(newrun);
    //addChildControllableContainer(newrun);
    //runs.add(newrun);
    
  }

  if (data.getDynamicObject()->hasProperty("nRuns"))
    nRuns->setValue(data.getDynamicObject()->getProperty("nRuns"));
  
  //if (data.getDynamicObject()->hasProperty("pathToEmergens"))
  //  pathToEmergens->setValue(data.getDynamicObject()->getProperty("pathToEmergens"));
  
  if (data.getDynamicObject()->hasProperty("xAxis"))
    xAxis->setValue(data.getDynamicObject()->getProperty("xAxis"));
  
  if (data.getDynamicObject()->hasProperty("yAxis"))
    yAxis->setValue(data.getDynamicObject()->getProperty("yAxis"));
  
  if (data.getDynamicObject()->hasProperty("pathToCSV"))
    pathToCSV->setValue(data.getDynamicObject()->getProperty("pathToCSV"));
  */
  
}





var NEP::getJSONData(bool includeNonOverriden)
{
  /*
  // add saved material specific to daughter class
  var data = new DynamicObject();
  //data.getDynamicObject()->setProperty("pathToEmergens", pathToEmergens->stringValue());
  data.getDynamicObject()->setProperty("xAxis", xAxis->getValue());
  data.getDynamicObject()->setProperty("yAxis", yAxis->getValue());
  data.getDynamicObject()->setProperty("pathToCSV", pathToCSV->stringValue());
  data.getDynamicObject()->setProperty("nRuns", nRuns->intValue());

  var vruns;
  for (auto& r : runs)
  {
    var v = r->getJSONData();
    vruns.append(v);
  }
  data.getDynamicObject()->setProperty("runs", vruns);

  
  return data;
  */
  
}





void NEP::newMessage(const Simulation::SimulationEvent &ev)
{
  switch (ev.type)
  {
    case Simulation::SimulationEvent::UPDATEPARAMS:
    {
      updateSteadyStateList();
    }
    case Simulation::SimulationEvent::WILL_START:
    {
    }
    case Simulation::SimulationEvent::STARTED:
    {
    }
    case Simulation::SimulationEvent::NEWSTEP:
    {
    }
    case Simulation::SimulationEvent::FINISHED:
    {
    }
  }
}


void NEP::newMessage(const ContainerAsyncEvent &e)
{

}

