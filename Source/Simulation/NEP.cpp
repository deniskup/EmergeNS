//  NEP.cpp
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//

#include "NEP.h"
#include "Simulation.h"
using namespace juce;

juce_ImplementSingleton(NEP);


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
  
  stopDescent = addTrigger("Stop Descent", "Manually stop the descent algorithm");
  test = addTrigger("test", "");
  
  //start_heteroclinic_study = addTrigger("Heteroclinic study", "Produces most probable trajectories between two fixed points");
    
  // enum parameters = steady states
  sst_stable = addEnumParameter("Stable steady state", "Choose stable fixed point to start the NEP algorithm from");
  sst_saddle = addEnumParameter("Unstable steady state", "Choose unstable fixed point to start the NEP algorithm from");
  
  Niterations = addIntParameter("Max. iterations", "Maximum of iterations the descent will perform", 10);
  
  nPoints_start = addIntParameter("Sampling points", "Number of sampling points used for the descent", 10);
  
  nPoints_max = addIntParameter("Max. sampling", "Maximum number of sampling points used by the descent", 100);
  
  initialConditions = addEnumParameter("Initial condition", "Choose how the optimal trajectory is initialized for the descent.");

  //cutoffFreq = addFloatParameter("Cutoff frequency", "Cutoff frequency normalized to a sampling rate of 1", 0.05);

  //maxcutoffFreq = addFloatParameter("Max. cutoff frequency", "max. frequency of low-pass filtering, after what descent will stop.", 100.);
  
  solverType = addEnumParameter("Solver type", "Solver lib. and method to use for the descent");
  
  action_threshold = addStringParameter("Action threshold", "Descent will update parameters when action threshold is reached", "1e-5");
  
  stepDescentThreshold = addStringParameter("Step descent threshold", "Descent will update update parameters when step gets below threshold.", "1e-5");
  
  //timescale_factor = addFloatParameter("Time scale factor", "Descent behaves badly when kinetics rate constants are too low. A solution consists in scaling up those constants.", 100.);
  
  stepDescentInitVal = addFloatParameter("Initial step descent", "Descent will try proceeding with user indicated step, and will decrease it following the use of a backtracking method if this step is too large.", 1.);
  
  maxPrinting = addBoolParameter("Maximum Printing", "Will print whole descent in a DEBUG.TXT file.", false);
    
  // set options
  updateSteadyStateList();
  
  initialConditions->clearOptions();
  initialConditions->addOption("Straigth line", 0);
  initialConditions->addOption("Deterministic trajectory", 1);
  
  solverType->clearOptions();
  solverType->addOption("GSL Brut force - NLS", 0);
  solverType->addOption("GSL Decouple t/p - NLS", 1);
  solverType->addOption("GSL Decouple t/p - Minimizer", 2);

  
  // set this class as simulation listener
  //simul->addAsyncSimulationListener(this);
  //simul->addAsyncContainerListener(this);
  
  kinetics = new KineticLaw(false, 0.);
  
  d_action_threshold = convertStringToDouble(action_threshold->stringValue());
  d_stepDescentThreshold = convertStringToDouble(stepDescentThreshold->stringValue());
  
 

  
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
  if (p == action_threshold)
  {
    d_action_threshold = convertStringToDouble(action_threshold->stringValue());
  }
  else if (p == stepDescentThreshold)
  {
    d_stepDescentThreshold = convertStringToDouble(stepDescentThreshold->stringValue());
  }
  
}


void NEP::onContainerTriggerTriggered(Trigger* t)
{
  if (t == startDescent)
  {
    stopThread(10);
    state = Descending;
    startThread();
  }
  else if (t == start_heteroclinic_study)
  {
    heteroclinic_study = true;
    stopThread(10);
    startThread();
  }
  else if (t == stopDescent)
  {
    stop();
  }
  else if (t == test)
  {
    //StateVec v = {1., 1., 1.};
    //dsp::Matrix<double> hh = buildOrthogonalBasis(v);
    debuggingFunction();
  }
}



void NEP::onChildContainerRemoved(ControllableContainer* cc)
{
  
}



void NEP::reset()
{
  // reset previous calculations
  actionDescent.clear();
  trajDescent.clear();
  dAdqDescent.clear();
  dAdqDescent_filt.clear();
  gslStatus_descent.clear();
  collinearityStatus_descent.clear();
  residuals_H_descent.clear();
  residuals_p_descent.clear();
  
  g_qcurve.clear();
  g_pcurve.clear();
  g_times.clear();
  dAdq.clear();
  dAdq_filt.clear();
  action = 10.;
  length_qcurve = 0.;
  stepDescent = stepDescentInitVal->floatValue();
  stepDescentInit_dynamic = stepDescentInitVal->floatValue();
  //cutoffFreq->setValue(0.05);
  nPoints = nPoints_start->intValue();
  tolerance_mu = tolerance_mu_init;
}


void NEP::stop()
{
  state = Idle;
  LOG("Descent algorithm stops");
  signalThreadShouldExit();
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
    cout << "WILL DO MAX PRINTINGS" << endl;
    debugfile.open("./debug/DEBUG.txt", ofstream::out | ofstream::trunc);
    debugfile << "\t\t\t------ DEBUG ------" << endl;
    debugfile << "Descent parameters" << endl;
    debugfile << "Sampling points : " << nPoints_max->intValue() << endl;
    //debugfile << "Max. sampling : " << nPoints_max->intValue() << endl;
  }
  
  // init concentration curve
  LOG("init g_qcurve");
  try
  {
    initConcentrationCurve();
  } catch (const std::exception& e)
  {
    LOGWARNING(e.what());
    return;
  }
  
  // message to async
  nepNotifier.addMessage(new NEPEvent(NEPEvent::WILL_START, this));
  
  // set normalisation factor in order to have all kinetic constants of order 1
  setTimeNormalizationFactor();
  LOG("Using time normalization factor : " + to_string(timescale_factor));
  
  
  // start descent
  int count = 0;
  while (descentShouldContinue(count+1) && !threadShouldExit())
  {
    count++;
    LOG("\niteration #" + to_string(count-1));
    
    if (count>1)
    {
      LOG("Using backtracking method with initial step " + to_string(stepDescentInit_dynamic));
      stepDescent = backTrackingMethodForStepSize(g_qcurve);
      LOG("using step = " + to_string(stepDescent));
      updateOptimalConcentrationCurve(g_qcurve, stepDescent);
    }
    
    if (maxPrinting->boolValue())
    {
      debugfile << "\nIteration " << count << endl;
      debugfile << "-- concentration curve --" << endl;
      debugfile << "[ ";
      for (int p=0; p<g_qcurve.size(); p++)
      {
        debugfile << "(";
        int c=0;
        for (auto & qm : g_qcurve.getUnchecked(p))
        {
          string closebracket = (p == g_qcurve.size()-1 ? ") " : "), ");
          string comma = (c == g_qcurve.getUnchecked(p).size()-1 ? closebracket : ",");
          debugfile << qm << comma ;
          c++;
        }
      }
      debugfile << " ]" << endl;
    }
    
    // lift current trajectory to full (q ; p; t) space
    // this function updates global variables g_pcurve and times
    LOG("lifting trajectory");
    //LiftTrajectoryOptResults liftoptres = liftCurveToTrajectoryWithNLOPT();
    LiftTrajectoryOptResults liftoptres = liftCurveToTrajectoryWithGSL(g_qcurve, true);
    
    
    
    // for NEPUI
    double successFrac = 0.;
    double d_npoints = (double) nPoints - 1.;
    jassert(d_npoints>0.);
    for (int k=0; k<liftoptres.gslStatus.size()-1; k++)
    {
     if (liftoptres.gslStatus.getUnchecked(k) == 1)
       successFrac += 1. / d_npoints;
    }
    if (isinf(successFrac) || isnan(successFrac))
      successFrac = 0.;
    successFrac *= 100.;
    cout << "Convergence Fraction = " << successFrac << "%" << endl;
    
    // update global variable with lift results
    g_pcurve = liftoptres.pcurve;
    g_times = liftoptres.times;
    
    // keep track of trajectory update in (q ; p) space
    Trajectory newtraj;
    Array<double> hams;
    for (int point=0; point<nPoints; point++)
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
    
    // keep track of gsl convergence status
    gslStatus_descent.add(liftoptres.gslStatus);
    collinearityStatus_descent.add(liftoptres.collinearity);
    
    // Keep track of residuals
    residuals_H_descent.add(liftoptres.residuals_H);
    residuals_p_descent.add(liftoptres.residuals_p);
    
    /*
    if (maxPrinting->boolValue())
    {
      debugfile << "-- momentum curve --" << endl;
      debugfile << "[ ";
      for (int p=0; p<nPoints; p++)
      {
        debugfile << "(";
        int c=0;
        for (auto & pm : g_pcurve.getUnchecked(p))
        {
          string closebracket = (p == nPoints-1 ? ") " : "), ");
          string comma = (c == g_pcurve.getUnchecked(p).size()-1 ? closebracket : ",");
          debugfile << pm << comma ;
          c++;
        }
      }
      debugfile << " ]" << endl;
      debugfile << "-- time sampling --" << endl;
      debugfile << "[ ";
      //cout << "times.size = " << g_times.size() << endl;
      for (int p=0; p<nPoints; p++)
      {
        string comma = (p == nPoints-1 ? "" : ", ");
        debugfile << g_times.getUnchecked(p) << comma ;
      }
      debugfile << " ]" << endl;
    }
    */
  
    
    // calculate action value
    LOG("calculating action");
    Array<double> newcumulaction = calculateAction(g_qcurve, g_pcurve, g_times);
    double newaction = newcumulaction.getLast();
    double diffAction = action - newaction;
    LOG("action = " + to_string(newaction));
    //LOG("delta action = " + to_string(diffAction));
    
    if (isnan(newaction)|| isnan(diffAction))
    {
      LOGWARNING("Action is nan. Descent probably diverged. Stopping descent.");
      signalThreadShouldExit();
    }
    
    if (newaction<0.)
    {
      LOGWARNING("Action is <0. Probably wrong. Stopping descent.");
      signalThreadShouldExit();
    }
      
    actionDescent.add(newcumulaction);
    action = newaction;
    
    if (maxPrinting->boolValue())
    {
      debugfile << "-- Action --" << endl;
      debugfile << "S = " << newaction << " & deltaS = " << diffAction << endl;
    }
    
    //LOG("action = " + to_string(newaction) + ". deltaS = " + to_string(diffAction));
    
    // message to async to monitor the descent
    double dummy_cutoffFreq = 1.;
    nepNotifier.addMessage(new NEPEvent(NEPEvent::NEWSTEP, this, count, newaction, dummy_cutoffFreq, nPoints, metric, successFrac));
    
    
    // check algorithm descent status
    bool shouldUpdate = descentShouldUpdateParams(diffAction);
    if (shouldUpdate && count>1)
    {
      //LOG("descentUpdatesParams");
      //updateDescentParams();
      
      // resample the concentration and momentum curves
      //LOG("Resampling in time uniform with " + to_string(nPoints) + " points.");
      //resampleInTimeUniform(g_qcurve, nPoints);
      //cout << "sizes of (q, p) : " << g_qcurve.size() << " " << g_pcurve.size() << endl;
      //resampleInSpaceUniform(g_qcurve, nPoints);
      
     
      
      // must move directly to next iteration
      //continue;
      
      // the following I do not perform
      //resampleInTimeUniform(g_qcurve, g_qcurve.size());
      //lowPassFiltering(g_qcurve, true);
      //resampleInSpaceUniform(g_qcurve, g_qcurve.size());
      //liftCurveToTrajectoryWithGSL();
    }
    
    
    
    // functional gradient dA / dq
    for (int point=0; point<nPoints; point++)
    {
      StateVec dHdqk = evalHamiltonianGradientWithQ(g_qcurve.getUnchecked(point), g_pcurve.getUnchecked(point));
      StateVec dpdtk;
      dpdtk.insertMultiple(0, 0., nPoints);
      if (point>0 && point<(nPoints-1))
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
    //dAdqDescent.add(dAdq);
    
    // filter gradient
    dAdq_filt = dAdq;
    //lowPassFiltering(dAdq_filt, false);
    //dAdqDescent_filt.add(dAdq_filt);
   
    if (maxPrinting->boolValue())
    {
      debugfile << "-- dAdq --" << endl;
      debugfile << "[ ";
      for (int p=0; p<nPoints; p++)
      {
        debugfile << "(";
        StateVec dAdqk = dAdq.getUnchecked(p);
        int c=0;
        for (auto & coord : dAdqk)
        {
          string closebracket = (p == nPoints-1 ? ") " : "), ");
          string comma = ( c==dAdqk.size()-1 ? closebracket : "," );
          debugfile << coord << comma;
          c++;
        }
      }
      debugfile << " ]" << endl;
    }
        
  } // end while
  
  //cout << actionDescent.size() << " --- " << trajDescent.size() << endl;
  
  if (maxPrinting)
  {
    debugfile.close();
  }
  
  // save descent algorithm results into a file
  LOG("writing descent to file");
  writeDescentToFile();
  
  //stop();
  
  
}










void printLiftingJacobian_brutforce(gsl_multiroot_fdfsolver * s, EncapsVarForGSL ev, int n)
{
  StateVec p;
  for (int i=0; i<n-1; i++)
  {
    p.add(gsl_vector_get(s->x, i));
  }
  double mu = exp(gsl_vector_get(s->x, n-1));
  
  dsp::Matrix<double> jaco = calculateLiftingJacobian_brutforce(ev, p, mu, n);
  
  cout << "J = " << endl;
  for (int i=0; i<n; i++)
  {
    for (int j=0; j<n; j++)
    {
      cout << jaco(i, j) << " ";
    }
    cout << endl;
  }
}

void printLiftingJacobian(gsl_multiroot_fdfsolver * s, EncapsVarForGSL ev, int n)
{
  StateVec p;
  for (int i=0; i<n; i++)
  {
    p.add(gsl_vector_get(s->x, i));
  }
  
  StateVec q = ev.qcenter;
  StateVec dHdp = ev.nep->evalHamiltonianGradientWithP(q, p);
  dsp::Matrix<double> hessian = ev.nep->evalHamiltonianHessianWithP(q, p);
  
  dsp::Matrix<double> jaco = calculateLiftingJacobian(dHdp, hessian, ev.B, ev.pnorm, ev.equation_norm, n);
  
  cout << "--- Jacobian ---" << endl;
  cout << "J = " << endl;
  for (int i=0; i<jaco.getNumRows(); i++)
  {
    for (int j=0; j<jaco.getNumColumns(); j++)
    {
      cout << jaco(i, j) << " ";
    }
    cout << endl;
  }
  
}


LiftTrajectoryResults NEP::nonLinearEquationSolving(int nls)
{
  juce::Array<LiftTrajectoryResults> liftResults;
  liftResults.resize(nPoints-1);
  
  for (int point=0; point<nPoints-1; point++) // n - 1 iterations
  {
    // calculate q, dq of current concentration curve
    StateVec q = qcurve.getUnchecked(point);
    StateVec qnext = qcurve.getUnchecked(point+1);
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
    ev.q = qcenter;
    ev.dq = deltaq;
    ev.epsilon = 1.;
    // momentum normalization initialized to unity
    Array<double> pnorm;
    pnorm.insertMultiple(0, 1., n-1);
    ev.pnorm = pnorm;
    // equation normalization
    Array<double> eqnorm;
    eqnorm.insertMultiple(0, 1., n);
    ev.equation_norm = eqnorm;
    
    pool.addJob(new NEPWorker(crn, liftResults.getReference(point), nls, point), true);
  }
  
  pool.waitForJobToFinish();
  
  
  
  
  
  
  
  LiftTrajectoryOptResults output;
  // build it from array liftResults

  return output;
  
}

LiftTrajectoryOptResults NEP::liftCurveToTrajectoryWithGSL(const Curve& qcurve, bool maxPrintingAllowed)
{
  
  
  
  //cout << "--- NEP::liftCurveToTrajectoryWithGSL() ---" << endl;
  //cout << "input qcurve size = " << qcurve.size() << endl;
  // dimension of the problem
  const int n = simul->entities.size() + 1; // number of entities + 1
  
  // GSL to find optimal momentum and dt associated to qcurve
  LiftTrajectoryOptResults liftResults = nonLinearEquationSolving(solverType->getValueDataAsEnum<int>());
  
  /*
  if (solverType->getValueDataAsEnum<int>() == 0)
    liftResults = findOptimalMomentumAndTime_brutforce(qcurve, n, maxPrintingAllowed);
  else if (solverType->getValueDataAsEnum<int>() == 1)
    liftResults = findOptimalMomentumAndTime_opt(qcurve, n-1, maxPrintingAllowed);
  else if (solverType->getValueDataAsEnum<int>() == 2)
    liftResults = findOptimalMomentumAndTime_LF(qcurve, n-1, maxPrintingAllowed);
  else
    liftResults = findOptimalMomentumAndTime_brutforce(qcurve, n, maxPrintingAllowed);
  */
  // for debugging
  if (maxPrinting->boolValue() && maxPrintingAllowed)
  {
    debugfile << "-- lifting optima found --" << endl;
    debugfile << "p* = [ ";
    int p=0;
    for (auto & ppoint : liftResults.opt_momentum)
    {
      debugfile << "(";
      int c=0;
      for (auto & pm : ppoint)
      {
        string closebracket = (p == liftResults.opt_momentum.size()-1 ? ") " : "), ");
        string comma = ( c==ppoint.size()-1 ? closebracket : "," );
        debugfile << pm << comma;
        c++;
      }
      p++;
    }
  debugfile << " ]" << endl;
  debugfile << "dt = [ ";
  p=0;
  for (auto & tpoint : liftResults.opt_deltaT)
  {
    string comma = (p == liftResults.opt_deltaT.size()-1 ? "" : ", ");
    debugfile << tpoint << comma;
    p++;
  }
  debugfile << " ]" << endl;
  }
  

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
  for (int k=1; k<nPoints; k++) // nPoints-1 iterations
  {
    if (k==0)
      continue;
        
    // handle time
    sumtime += liftResults.opt_deltaT.getUnchecked(k-1);
    times.add(sumtime);
    
    // handle momentum, mean between current and next p
    if (k==nPoints-1) // force last momentum vec to be 0
      pcurve.add(nullP);
    else
    {
      StateVec meanP;
      for (int m=0; m<liftResults.opt_momentum.getUnchecked(k).size(); m++)
      {
        double pm = 0.5*(liftResults.opt_momentum.getUnchecked(k-1).getUnchecked(m) + liftResults.opt_momentum.getUnchecked(k).getUnchecked(m));
        meanP.add(pm);
      }
      pcurve.add(meanP);
    }
  }

  jassert(pcurve.size() == qcurve.size());
  jassert(times.size() == qcurve.size());
  
  // for debugging
  if (maxPrinting->boolValue() && maxPrintingAllowed)
  {
    debugfile << "-- Built momentum curve --" << endl;
    debugfile << "p = [ ";
    int p=0;
    for (auto & ppoint : pcurve)
    {
      debugfile << "(";
      int c=0;
      for (auto & pm : ppoint)
      {
        string closebracket = (p == pcurve.size()-1 ? ") " : "), ");
        string comma = ( c==ppoint.size()-1 ? closebracket : "," );
        debugfile << pm << comma;
        c++;
      }
      p++;
    }
  debugfile << " ]" << endl;
  }
  
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
  if (maxPrinting->boolValue() && maxPrintingAllowed)
  {
    debugfile << "-- Filtered momentum curve --" << endl;
    debugfile << "p_av = [ ";
    int p=0;
    for (auto & ppoint : av_pcurve)
    {
      debugfile << "(";
      int c=0;
      for (auto & pm : ppoint)
      {
        string closebracket = (p == av_pcurve.size()-1 ? ") " : "), ");
        string comma = ( c==ppoint.size()-1 ? closebracket : "," );
        debugfile << pm << comma;
        c++;
      }
      p++;
    }
  debugfile << " ]" << endl;
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
  //LiftTrajectoryOptResults output;
  //output.opt_deltaT = vec_dt;
  //output.opt_momentum = vec_pstar;
  //output.pcurve = pcurve;
  //output.times = times;
  
  liftResults.pcurve = pcurve;
  liftResults.times = times;
  
  
  
  return liftResults;
  
}



void NEP::setTimeNormalizationFactor()
{
  //LOGWARNING("timescale always set to 1.");
  //timescale_factor = 1.;
  //return;
  
  double meanK = 0.;
  double nreac = 0.;
  // loop over reactions
  for (auto & reaction : simul->reactions)
  {
    nreac++;
    meanK += reaction->assocRate;
    
    if (reaction->isReversible)
    {
      nreac++;
      meanK += reaction->dissocRate;
    }
  }
  
  // loop over entities
  for (auto & ent : simul->entities)
  {
    // destruction
    nreac++;
    meanK += ent->destructionRate;
    
    // creation
    if (ent->creationRate > 0.)
    {
      nreac++;
      meanK += ent->creationRate;
    }
  }
  
  if (nreac > 0. && meanK > 0.)
  {
    meanK /= nreac;
    timescale_factor = 1. / meanK;
  }
  else
  {
    timescale_factor = 1.;
  }
}




void NEP::initConcentrationCurve()
{
  // read init and final curve points from enum parameters
  int sstI = sst_stable->intValue();
  int sstF = sst_saddle->intValue();
  
  // add guard if initial steady state is unstable or final steady state is stable
  if (!simul->steadyStatesList->arraySteadyStates.getUnchecked(sstI).isStable || simul->steadyStatesList->arraySteadyStates.getUnchecked(sstF).isStable)
  {
    SteadyState sI = simul->steadyStatesList->arraySteadyStates.getUnchecked(sstI);
    SteadyState sF = simul->steadyStatesList->arraySteadyStates.getUnchecked(sstF);
    LOG("Initial steady state stability : " + to_string(sI.isStable) + ". Coordonates : ");
    simul->steadyStatesList->printOneSteadyState(sI);
    LOG("Final steady state stability : " + to_string(sF.isStable) + ". Coordonates : ");
    simul->steadyStatesList->printOneSteadyState(sF);
    throw std::runtime_error("Initial steady state should be stable, and final steady state unstable. Cannot perform descent.");
  }
  
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
  double NN = (double) nPoints;
  jassert(nPoints>1);
  
  if (initialConditions->getValueKey() == "Deterministic trajectory")
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
    
    // set first point of qcurve = qF (unstable state)
    g_qcurve.add(qF);
    
    // set initial concentration of entities to be very close from qF in the direction of qI
    Curve sl = {qI, qF};
    double L = curveLength(sl);
    jassert(L>0.);
    for (int i=0; i<qI.size(); i++)
    {
      double ui = qF.getUnchecked(i) + 0.01 * ( qI.getUnchecked(i)-qF.getUnchecked(i) ) / L;
      entities[i]->concent.setUnchecked(0, ui);
      //entities[i]->startConcent.setUnchecked(0, ui);
    }
    
    
    // deterministic dynamics of the system until a stationnary state is reached
    double distance = 1000.;
    double precision = 1e-5;
    double timeout = (double) simul->dt->floatValue() * 50000;
    double t = 0.;
    int count = 0;
    bool delay = true; // require the deterministic search to run a minimum amount of time
    // otherwise, too close from an unstable steady state, variation might be too small
    while (distance>precision || delay)
    {
      count++;
      t += (double) simul->dt->floatValue();
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
        double deltaC = ent->concent.getUnchecked(0)-ent->previousConcent.getUnchecked(0);
        distance += deltaC*deltaC;
      }
      distance = sqrt(distance);
    } // end while
    
    // find in which steady state the system ended
    int reachedSST = -1;
    double dmin = 10000.;
    count = 0;
    for (auto & sst : simul->steadyStatesList->arraySteadyStates)
    {
      double d = 0.;
      for (auto & p : sst.state)
      {
        int entID = p.first->idSAT;
        SimEntity * se = entities.getUnchecked(entID);
        double dc = se->concent.getUnchecked(0) - p.second;
        d += dc*dc;
      }
      d = sqrt(d);
  
      if (d<dmin)
      {
        dmin = d;
        reachedSST = count;
      }
      count++;
    }
    
    if (reachedSST != sstI)
    {
      LOGWARNING("System converged to steady state " + to_string(reachedSST) + " while steady state " + to_string(sstI) + " was specified.");
      throw std::runtime_error("Deterministic trajectory method failed to init. concentration trajectory. System did not converge to the correct steady state.");
    }
    
    // set last point of qcurve = qI
    g_qcurve.add(qI);

    // reverse the direction of concentration curve
    std::reverse(g_qcurve.begin(), g_qcurve.end());
    
    // resample qcurve
    resampleInSpaceUniform(g_qcurve, nPoints);
  }
  else // use straightline
  {
    for (int point=0; point<nPoints; point++)
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
    sampleRate = (double) nPoints / length_qcurve;
  else
  {
    LOGWARNING("qcurve has null length !!");
    sampleRate = 1000.;
  }
  /*
  // debugging
  cout << "curve size after init : " << g_qcurve.size() << ". nPoints = " << nPoints << endl;
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
  //cout << "filtering concentration curve" << endl;
  // filter the gradient
  //filter.setCutoffFrequency(cutoffFreq->floatValue());
  //filter.prepare(sampleRate, simul->entities.size());
  //filter.setSamplingRate(sampleRate);
  //filter.setCutoffFrequency(cutoffFreq->floatValue());
  //filter.process(g_qcurve);
}


void NEP::updateDescentParams()
{
  //cout << "updating descent params" << endl;
  //cutoffFreq->setValue(cutoffFreq->floatValue() + 0.01);
  //nPoints += 20;
  //nPoints = std::min(nPoints, nPoints_max->intValue());
  tolerance_mu /= 10.;
  
  //std::ostringstream oss;
  //oss << std::scientific << std::setprecision(4) << tolerance_mu;
  //LOG("tolerance on H(p,q)=0 residual is : " + oss.str());
}


bool NEP::descentShouldUpdateParams(double diffAction)
{
  //cout << diffAction << " " << d_action_threshold << " || " << stepDescent << " " << d_stepDescentThreshold << endl;
  bool b1 = (diffAction<d_action_threshold || stepDescent<d_stepDescentThreshold);
  bool b2 = nPoints < nPoints_max->intValue();
  return (b1 && b2);
  //return ((diffAction<d_action_threshold || stepDescent<d_stepDescentThreshold));
}

bool NEP::descentShouldContinue(int step)
{
  //return (step<=Niterations->intValue() && tolerance_mu > tolerance_mu_min);
  return (step<=Niterations->intValue());
}


void NEP::writeDescentToFile()
{
  // open output file
  system("mkdir -p descent");
  string filename = "descent/action-functionnal-descent_";
  filename += to_string(sst_stable->intValue()) + "->" + to_string(sst_saddle->intValue());
  filename += "_" + to_string(nPoints_max->intValue());
  filename += ".csv";
  ofstream historyFile;
  historyFile.open(filename, ofstream::out | ofstream::trunc);
  
  historyFile << "Descent characteristics used :" << endl;
  historyFile << "Number of iterations : " << Niterations->intValue() << endl;
  historyFile << "Initial condition : " << initialConditions->getValueKey() << endl;
  historyFile << "Action threshold : " << action_threshold->stringValue() << endl;
  historyFile << "Timescale factor : " << timescale_factor << endl;
  historyFile << "Initial step descent : " << stepDescentInitVal->floatValue() << endl;
  historyFile << "###############" << endl;
  
  historyFile << "iteration,point,gslStatus,collinearStatus,action";
  for (auto & ent : simul->entities)
    historyFile << ",q_" << ent->name;
  for (auto & ent : simul->entities)
    historyFile << ",p_" << ent->name;
  //for (auto & ent : simul->entities)
  //  historyFile << ",dAdq_" << ent->name;
  //for (auto & ent : simul->entities)
  //  historyFile << ",dAdq_filt_" << ent->name;
  historyFile << ",res_H";
  for (auto & ent : simul->entities)
    historyFile << ",res_p_" << ent->name;
  historyFile << endl;
  
  //cout << "action descent size :" << actionDescent.size() << endl;
  //cout << "trajDescent descent size :" << trajDescent.size() << endl;
  //cout << "grad Descent size :" << dAdqDescent.size() << endl;
  //cout << "filtered grad Descent size :" << dAdqDescent_filt.size() << endl;
  jassert(actionDescent.size() == trajDescent.size());
  //jassert(actionDescent.size() == dAdqDescent.size());
  //jassert(actionDescent.size() == dAdqDescent_filt.size());
  jassert(actionDescent.size() == gslStatus_descent.size());
  jassert(actionDescent.size() == collinearityStatus_descent.size());
  jassert(actionDescent.size() == residuals_H_descent.size());
  jassert(actionDescent.size() == residuals_p_descent.size());
  
  //cout << actionDescent.size() << " " << gslStatus_descent.size() << " " << collinearityStatus_descent.size() << " ";
  //cout << residuals_H_descent.size() << " " << residuals_p_descent.size() << endl;
  
  int nPoints_descent = actionDescent.size();
  
  for (int iter=0; iter<nPoints_descent; iter++) // loop over descent iterations
  {
    int npoint_local = trajDescent.getUnchecked(iter).size();
    for (int point=0; point<npoint_local; point++) // loop over curve points
    {
      historyFile << iter << "," << point;
      historyFile << "," << gslStatus_descent.getUnchecked(iter).getUnchecked(point) << "," << collinearityStatus_descent.getUnchecked(iter).getUnchecked(point);
      historyFile << "," << actionDescent.getUnchecked(iter).getUnchecked(point);
      
      PhaseSpaceVec trajpq = trajDescent.getUnchecked(iter).getUnchecked(point);
      //StateVec dAdq_local = dAdqDescent.getUnchecked(iter).getUnchecked(point);
      //StateVec dAdq_filt_local = dAdqDescent_filt.getUnchecked(iter).getUnchecked(point);
      Array<double> resP = residuals_p_descent.getUnchecked(iter).getUnchecked(point);
      
      jassert(resP.size() == simul->entities.size());
      if (resP.size() != simul->entities.size())
        cout << resP.size() << " " << simul->entities.size() << endl;
      
      //cout << "trajectory size : " << trajpq.size() << endl;
      for (int m=0; m<trajpq.size()/2; m++)
        historyFile << "," << trajpq.getUnchecked(m);
      for (int m=trajpq.size()/2; m<trajpq.size(); m++)
        historyFile << "," << trajpq.getUnchecked(m);
      //for (int m=0; m<dAdq_local.size(); m++)
      //  historyFile << "," << dAdq_local.getUnchecked(m);
      //for (int m=0; m<dAdq_filt_local.size(); m++)
      //  historyFile << "," << dAdq_filt_local.getUnchecked(m);
      historyFile << "," << std::scientific << residuals_H_descent.getUnchecked(iter).getUnchecked(point);
      for (int m=0; m<resP.size(); m++)
        historyFile << "," << resP.getUnchecked(m);
      historyFile << std::defaultfloat << endl;
    } // end loop over points in current iteration
    //historyFile << endl;
  } // end loop over iterations
  
}









// update concentration curve as q^I = q^(I-1) - stepDescent * dAdq_filtered
//void NEP::updateOptimalConcentrationCurve(Curve & _qcurve, double step)
bool NEP::updateOptimalConcentrationCurve(Curve & _qcurve, double step)
{
  Curve newqcurve = _qcurve;
  bool updateAllowed = true;

  for (int k=0; k<nPoints; k++)
  {
    // update curve point k component wise
    StateVec newqk;
    if (k==0 || k==nPoints-1)
    {
      newqk = newqcurve.getUnchecked(k);
    }
    else
    {
      for (int m=0; m<newqcurve.getUnchecked(k).size(); m++)
      {
        //newqk.add( _qcurve.getUnchecked(k).getUnchecked(m) - step * dAdq_filt.getUnchecked(k).getUnchecked(m) );
        double q = newqcurve.getUnchecked(k).getUnchecked(m) - step * dAdq.getUnchecked(k).getUnchecked(m);
        if (q<0. && updateAllowed)
          updateAllowed = false;
        newqk.add(q);
      }
    }
    newqcurve.setUnchecked(k, newqk);
    //qcurve.add(newqk);
  }
  //length_qcurve = curveLength(qcurve);
  //if (length_qcurve>0.)
  //  sampleRate = (double) nPoints / length_qcurve;
  jassert(_qcurve.size() == nPoints);
  
  // do not update concentration curve
  if (updateAllowed)
    _qcurve = newqcurve;
  
  return updateAllowed;
  
}



//double NEP::calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t)
Array<double> NEP::calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t)
{
  //cout << "-- calculateAction() --" << endl;
  // check that pcurve, qcurve and tcurve have the same size
  jassert(qc.size() == pc.size());
  jassert(qc.size() == t.size());
  
  //cout << "--- calculate action ---" << endl;
  
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
  
  // use trapezoidal rule to calculate action = integral(0, T, p•dq - H*dt)
  double newaction = 0.;
  Array<double> cumul_action;
  cumul_action.add(0.);
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
    //cout << "p•dq = " << spdebug << "\tH_i "<< " = " << hamilt.getUnchecked(i) << ". dt = " << deltaTi << ". integrand = " << integrand << endl;
    newaction += integrand;
    cumul_action.add(newaction);
    //cout << "\tadding " << integrand << endl;
  }
  
  //cout << "action = " << newaction << endl;
  // update action value
  //action = newaction;
  // keep track of action history
  //actionDescent.add(newaction);
  
  //return newaction;
  return cumul_action;
  
}


//double NEP::backTrackingMethodForStepSize(const Curve& qc, const Curve& dAdq)
double NEP::backTrackingMethodForStepSize(const Curve& qc)
{
  // init step with previous value of stepDescent
  double step = stepDescentInit_dynamic;
  double minstep = 0.99*d_stepDescentThreshold;
  
  // time is such that minstep would be reached at last iteration
  int timeout = round(log(step/minstep) / log(2)) + 1;
  
  //cout << "NEP::backTrackingMethodForStepSize" << endl;
  //cout << "Init guess : " << step << endl;
  
  Array<double> cumulaction = calculateAction(qc, g_pcurve, g_times);
  double currentaction = cumulaction.getLast();
  /* debugging
  cout << "current action = " << currentaction << endl;
  cout << "current q = " ;
  for (auto & qm : qc.getUnchecked(nPoints/2))
    cout << qm << " ";
  cout << endl;
  cout << "deltaq = " ;
  for (auto & qm : deltaqc.getUnchecked(nPoints/2))
    cout << qm << " ";
  cout << endl;
  cout << "p = " ;
  for (auto & pm : g_pcurve.getUnchecked(nPoints/2))
    cout << pm << " ";
  cout << endl;
  cout << "t = " << g_times.getUnchecked(nPoints/2) << endl;
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
    
    //cout << "trying step = " << step << endl;
    
    // update concentration curve corresponding to current step
    Curve newcurve = qc;
    bool updateIsValid = updateOptimalConcentrationCurve(newcurve, step);
    //cout << "update is Valid : " << updateIsValid << endl;
    
    if (!updateIsValid)
    {
      step *= 0.5;
      continue;
    }
    
    // find the corresponding lifted full trajectory, without updating global variables
    LiftTrajectoryOptResults liftResults = liftCurveToTrajectoryWithGSL(newcurve, false);
    
    /* debugging
    cout << "new q = ";
    for (auto & qm : newcurve.getUnchecked(nPoints/2))
      cout << qm << " ";
    cout << endl;
    cout << "new p = " ;
    for (auto & pm : g_pcurve.getUnchecked(nPoints/2))
      cout << pm << " ";
    cout << endl;
    cout << "new t = " << times.getUnchecked(nPoints/2) << endl;
    */
    
    /*
    // sanity check
    for (int point=0; point<nPoints; point++)
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
    Array<double> newcumulaction = calculateAction(newcurve, liftResults.pcurve, liftResults.times);
    double newact = newcumulaction.getLast();
    //cout << "iter = " << iter << ". step = " << step << ". new action = " << newact << " vs current action = " << currentaction << endl;
    if (newact>=currentaction || newact<0.)
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

  if (step<d_stepDescentThreshold)
  {
    step = 0.;
    stepDescentInit_dynamic *= 0.5;
  }
  if (step == stepDescentInit_dynamic)
  {
    stepDescentInit_dynamic *= 2.;
  }
  
  
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


void NEP::resampleInTimeUniform(Array<StateVec>& signal, int newsize)
{
  if (signal.size()<2)
    return;
  
  if (signal.size() != g_times.size())
  {
    LOGWARNING("Cannot resample in time uniform, array sizes do not match.");
    return;
  }
  
  if (newsize < 2)
  {
    LOGWARNING("Cannot perform resampling with only 2 points. Exit.");
    return;
  }
  
  if (newsize == signal.size())
    return;
  
  //cout << "NEP::resampleInTimeUniform()" << endl;
  //cout << "input = ";
  //for (int i=0; i<signal.size(); i++)
  //{
   // for (int j=0; j<signal.getUnchecked(i).size(); j++)
   // {
   //   string comma = (j==signal.getUnchecked(i).size()-1 ? "\n" : " , ");
   //   cout << signal.getUnchecked(i).getUnchecked(j) << comma;
   // }
  //}
  
  
  //int N = signal.size();
  int dim = signal.getUnchecked(0).size();
  double d_newsize =  (double) newsize;
  double ti = g_times.getFirst();
  double tf = g_times.getLast();
  
  
  // init newtraj with null vectors
  Trajectory resampled_signal;
  resampled_signal.resize(newsize);
  for (int i=0; i<newsize; ++i)
  {
    StateVec nullvec;
    nullvec.insertMultiple(0, 0., dim);
    resampled_signal.setUnchecked(i, nullvec);
  }
  
  // cumulative times of input signals
  Array<double> cumulative_times(g_times);
  
  //cout << "tvec : ";
  //for (auto & el : g_times)
   // cout << el << " ";
  //cout << endl;
  
  for (int k=0; k<newsize; k++)
  {
    // linear timing between ti and tf
    double tk = ti + (double)k * (tf-ti)/(d_newsize-1.);
        
    // find closest matching index in cumulative length array
    auto it = lower_bound(cumulative_times.begin(), cumulative_times.end(), tk);
    int closest = (int) distance(cumulative_times.begin(), it) - 1;
    closest = max(0, min(closest, (int)cumulative_times.size()-2)); // make sure closest is properly bounded
    
    //cout << "k : " << k << ". tk = " << tk << ". closest = " << closest << " & signal.size = " << signal.size() << endl;
    // linear interpolation
    double t_inf = cumulative_times.getUnchecked(closest);
    double t_sup = cumulative_times.getUnchecked(closest+1);
    double alpha = (t_sup != t_inf) ? (tk - t_inf) / (t_sup - t_inf) : 0.0;
    alpha = max(0., min(1., alpha));
    
    if (k==0)
    {
      resampled_signal.setUnchecked(k, signal.getFirst());
    }
    else if (k==newsize-1)
    {
      resampled_signal.setUnchecked(k, signal.getLast());
    }
    else
    {
      // interpolate between q[closest] and q[closest+1]
      for (int m=0; m<signal.getUnchecked(0).size(); m++)
      {
        double val = signal.getUnchecked(closest).getUnchecked(m) + alpha*(signal.getUnchecked(closest+1).getUnchecked(m)-signal.getUnchecked(closest).getUnchecked(m));
        resampled_signal.getReference(k).setUnchecked(m, val);
      } // end loop over dimension of the system
    } // end if
  } // end loop over new size
  

  

  // modify input signal
  signal.resize(newsize);
  for (int i=0; i<signal.size(); i++)
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
  */
  
  
}
/*

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
  //cout << "NEP::lowPassFiltering() 1st point : ";
  //for (auto & p : firstpoint)
  //  cout << p << " ";
  //cout << endl;
  //cout << "NEP::lowPassFiltering() last point : ";
  //for (auto & p : lastpoint)
  //  cout << p << " ";
  //cout << endl;
  
  
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
    for (int m=0; m<dim; m++)
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
    
    //for (int i=0; i<data.size(); ++i)
   // {
   //   double x = data[i];
   //   for (auto& f : filters)
   //     x = f.processSample(x);
   //   data.set(i, x);
   // }
    
    
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


*/




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
  for (int st=0; st<5000; st++)
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
  //liftCurveToTrajectoryWithNLOPT_old();
  liftCurveToTrajectoryWithGSL(g_qcurve, true);
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


void NEP::debuggingFunction()
{
  simul->affectSATIds();
  
  //StateVec qi = {1.58916000, 1.03974000};
  //StateVec pi = {0.01967720, 0.00082215};
  
  StateVec qi = {1.58310479, 1.04183355};
  StateVec pi = {0.01985969, 0.00110143};
  
  
  
  pair<Trajectory, Trajectory> eom = integrateHamiltonEquations(qi, pi);
  
  std::system("mkdir -p ./hamilton-eq-of-motion");
  
  ofstream output;
  output.open("./hamilton-eq-of-motion/hamilton_EoM_gagrani.csv", ofstream::out | ofstream::trunc);
  
  output << "point,isForward,q_X1,q_X2,p_X1,p_X2" << endl;
  
  cout << "traj forward : " << eom.first.size() << endl;
  cout << "traj backward : " << eom.second.size() << endl;
  
  // forward traj
  for (int k=0; k<eom.first.size(); k++)
  {
    PhaseSpaceVec psv = eom.first.getUnchecked(k);
    output << k << "," << true;
    for (auto & el : psv)
      output << "," << el;
    output << endl;
  }
  
  // backward traj
  for (int k=0; k<eom.second.size(); k++)
  {
    PhaseSpaceVec psv = eom.second.getUnchecked(k);
    output << k << "," << false;
    for (auto & el : psv)
      output << "," << el;
    output << endl;
  }
  
  output.close();
  
}


void NEP::loadJSONData(var data, bool createIfNotThere)
{
  updateSteadyStateList();
  // call mother class
  ControllableContainer::loadJSONData(data);
}
