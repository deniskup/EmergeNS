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
  
  nPointsUI = addIntParameter("Sampling points", "Number of sampling points used for the descent", 10);
  
  //nPoints_max = addIntParameter("Max. sampling", "Maximum number of sampling points used by the descent", 100);

  useChangeOfVariable = addBoolParameter("Use change of variable", "Change variable (p, s) --> (u, mu) with u = exp(p) and mu = exp(s) for the optimization.", false);
  
  initialConditions = addEnumParameter("Initial condition", "Choose how the optimal trajectory is initialized for the descent.");

  //cutoffFreq = addFloatParameter("Cutoff frequency", "Cutoff frequency normalized to a sampling rate of 1", 0.05);

  //maxcutoffFreq = addFloatParameter("Max. cutoff frequency", "max. frequency of low-pass filtering, after what descent will stop.", 100.);
  
  solverType = addEnumParameter("Solver type", "Solver lib. and method to use for the descent");
  
  action_threshold = addStringParameter("Action threshold", "Descent will update parameters when action threshold is reached", "1e-5");
  
  stepDescentThreshold = addStringParameter("Step descent threshold", "Descent will update update parameters when step gets below threshold.", "1e-5");
  
  toleranceUI = addStringParameter("Tolerance for residuals", "Non-linear equations are solved up to this residual value.", "1e-8");
  
  //timescale_factor = addFloatParameter("Time scale factor", "Descent behaves badly when kinetics rate constants are too low. A solution consists in scaling up those constants.", 100.);
  
  stepDescentInitVal = addFloatParameter("Initial step descent", "Descent will try proceeding with user indicated step, and will decrease it following the use of a backtracking method if this step is too large.", 1.);
  
  maxPrinting = addBoolParameter("Maximum Printing", "Will print whole descent in a DEBUG.TXT file.", false);

  adaptiveStepDescent = addBoolParameter("Adaptive step", "Step descent initial guess increased for next iteration if it allowed for a valid descent iteration.", true);
    
  // set options
  updateSteadyStateList();
  
  initialConditions->clearOptions();
  initialConditions->addOption("Straigth line", 0);
  initialConditions->addOption("Deterministic trajectory", 1);
  initialConditions->addOption("Guess", 2);

  
  solverType->clearOptions();
  solverType->addOption("GSL Brut force - NLS", 0);
  solverType->addOption("GSL Decouple t/p - NLS", 1);
  solverType->addOption("GSL Decouple t/p - Minimizer", 2);
  solverType->addOption("IPOPT", 3);


  
  // set this class as simulation listener
  //simul->addAsyncSimulationListener(this);
  //simul->addAsyncContainerListener(this);
  
  kinetics = new KineticLaw(false, 0.);
  
  d_action_threshold = convertStringToDouble(action_threshold->stringValue());
  d_stepDescentThreshold = convertStringToDouble(stepDescentThreshold->stringValue());
  tolerance = convertStringToDouble(toleranceUI->stringValue());
 
  buildReactionNetworkSnapshot();
  nepsolver = new NEPSolver(crn);
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
  else if (p == toleranceUI)
  {
    tolerance = convertStringToDouble(toleranceUI->stringValue());
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


// CRN snapshots
// will have to update this when integrating heterogeneous space
void NEP::buildReactionNetworkSnapshot()
{
  crn.entities.clear();
  crn.reactions.clear();
  // clone entities
  for (auto & ent : simul->entities)
  {
    crn.entities.add(ent->clone().release());
  }
  
  for (auto & ent : crn.entities)
      ent->entity = nullptr; // just make sure this copied SimEntity will not interfere with Entity object
  
  // clone reactions
  for (auto & r : simul->reactions)
    {
      Array<SimEntity*> reactants;
      Array<SimEntity*> products;
      for (auto & e : r->reactants)
      {
        reactants.add(crn.entities[e->idSAT]);
      }
      for (auto & e : r->products)
      {
        products.add(crn.entities[e->idSAT]);
      }
      SimReaction * copyr = new SimReaction(reactants, products, r->assocRate ,  r->dissocRate,  r->energy);
      crn.reactions.add(copyr);
    }
}


void NEP::reset()
{
  // reset previous calculations
  actionDescent.clear();
  trajDescent.clear();
  smooth_pcurve_Descent.clear();
  timeDescent.clear();
  dAdqDescent.clear();
  dAdqDescent_dHdq.clear();
  dAdqDescent_dpdt.clear();
  dAdqDescent.clear();
  dAdqDescent_filt.clear();
  gslStatus_descent.clear();
  collinearityStatus_descent.clear();
  residuals_H_descent.clear();
  residuals_p_descent.clear();
  
  g_qcurve.clear();
  g_pcurve.clear();
  g_smooth_pcurve.clear();
  g_times.clear();
  dAdq.clear();
  dAdq_filt.clear();
  action = 10.;
  length_qcurve = 0.;
  stepDescent = stepDescentInitVal->floatValue();
  stepDescentInit_dynamic = stepDescentInitVal->floatValue();
  //cutoffFreq->setValue(0.05);
  nPoints = nPointsUI->intValue();
  //tolerance_mu = tolerance_mu_init;
  tolerance = convertStringToDouble(toleranceUI->stringValue());
  
  cout << "buildReactionNetworkSnapshot()" << endl;
  buildReactionNetworkSnapshot();
  cout << "setting reaction network to solver" << endl;
  nepsolver->setReactionNetwork(crn);
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
    debugfile << "Sampling points : " << nPointsUI->intValue() << endl;
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
  cout << "will set time normalization factor" << endl;
  setTimeNormalizationFactor();
  LOG("Using time normalization factor : " + to_string(crn.timescale_factor));
  
  
  // start descent
  int count = 0;
  while (descentShouldContinue(count+1) && !threadShouldExit())
  {
    count++;
    LOG("\niteration #" + to_string(count-1));

    LiftResults liftResults;
    bool liftSuccess = false;

    if (count>1)
    {
      LOG("Using backtracking method with initial step " + to_string(stepDescentInit_dynamic));
      stepDescent = backTrackingMethodForStepSize(g_qcurve, liftResults);
      liftSuccess = (stepDescent > 0.);
      LOG("using step = " + to_string(stepDescent));
      //stepDescent = stepDescentInitVal->floatValue();
      updateOptimalConcentrationCurve(g_qcurve, stepDescent);
    }

    // update step descent initial value if a valid step was taken
    if (liftSuccess)
    {
      // if step is smaller than initial value, use current value as a future initial value
      double compare = stepDescentInit_dynamic;
      if (stepDescent < compare)
      {
        if (adaptiveStepDescent->boolValue())
          stepDescentInit_dynamic = std::max(d_stepDescentThreshold*1.01, stepDescent);
        else
          stepDescentInit_dynamic *= 0.75;
      }
        
  
      // increase step initial value if 
      if (stepDescent == compare && adaptiveStepDescent->boolValue())
      {
        stepDescentInit_dynamic *= 1.25;
      }
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
    //LiftResults liftoptres = liftCurveToTrajectoryWithNLOPT();
    //LOGWARNING("Reseting lift success to false for debugging.");
    //liftSuccess = false; // just for debugging
    if (!liftSuccess)
    {
      LOG("Lift curve");
      liftResults = liftCurveWithGSL(g_qcurve, true, count); 
    }
    
    
    
    // for NEPUI
    double successFrac = 0.;
    double d_npoints = (double) nPoints - 1.;
    jassert(d_npoints>0.);
    for (int k=0; k<liftResults.collinearity.size()-1; k++)
    {
     if (liftResults.collinearity.getUnchecked(k) == 1)
       successFrac += 1. / d_npoints;
    }
    if (isinf(successFrac) || isnan(successFrac))
      successFrac = 0.;
    successFrac *= 100.;
    cout << "Convergence Fraction = " << successFrac << "%" << endl;
    
    // update global variable with lift results
    g_pcurve = liftResults.pcurve;
    g_smooth_pcurve = liftResults.smooth_pcurve;
    g_times = liftResults.times;
    
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
      hams.add(nepsolver->evalHamiltonian(g_qcurve.getUnchecked(point), g_pcurve.getUnchecked(point)));
    }
    //cout << "adding a trajectory of size : " << newtraj.size() << " = " << g_qcurve.size() << " + " << g_pcurve.size() << endl;
    trajDescent.add(newtraj);
    smooth_pcurve_Descent.add(g_smooth_pcurve);

    // keep track of times
    timeDescent.add(g_times);
    
    // keep track of gsl convergence status
    gslStatus_descent.add(liftResults.gslStatus);
    collinearityStatus_descent.add(liftResults.collinearity);
    
    // Keep track of residuals
    residuals_H_descent.add(liftResults.residuals_H);
    residuals_p_descent.add(liftResults.residuals_p);
    
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
    Array<double> newcumulaction = nepsolver->calculateAction(g_qcurve, g_pcurve, g_times);
    double newaction = newcumulaction.getLast();
    double diffAction = action - newaction;
    //LOG("action = " + to_string(newaction));
    //LOG("delta action = " + to_string(diffAction));
    std::cout << std::scientific << std::setprecision(10) << "action = " << newaction << std::endl;
    std::cout << "delta action = " << diffAction << endl;
    std::cout << std::fixed << std::endl;
    
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
      //liftCurveWithGSL();
    }
    
    
    
    // functional gradient dA / dq
    dAdq.clear();
    dAdq_filt.clear();
    juce::Array<StateVec> dAdq_H, dAdq_qt;
    for (int point=0; point<nPoints; point++)
    {
      StateVec dHdqk = nepsolver->evalHamiltonianGradientWithQ(g_qcurve.getUnchecked(point), g_pcurve.getUnchecked(point));
      StateVec dpdtk;
      dpdtk.insertMultiple(0, 0., nPoints);
      if (point>0 && point<(nPoints-1))
      {
        for (int m=0; m<dHdqk.size(); m++)
        {
          double dpm = liftResults.pstar.getUnchecked(point).getUnchecked(m) - liftResults.pstar.getUnchecked(point-1.).getUnchecked(m);
          double dtm = 0.5*(liftResults.dt.getUnchecked(point) + liftResults.dt.getUnchecked(point-1));
          dpdtk.setUnchecked(m, dpm/dtm);
        }
      }
      //cout << "point " << point << endl;
      StateVec dAdqk;
      StateVec dAdqk_H, dAdqk_qt;
      for (int m=0; m<dHdqk.size(); m++)
      {
        dAdqk.add(dHdqk.getUnchecked(m) + dpdtk.getUnchecked(m));
        dAdqk_H.add(dHdqk.getUnchecked(m));
        dAdqk_qt.add(dpdtk.getUnchecked(m));
        //cout << "\t" << -dHdqk.getUnchecked(m) << " " << - dpdtk.getUnchecked(m) << endl;
      }
      
      dAdq.add(dAdqk);
      dAdq_H.add(dAdqk_H);
      dAdq_qt.add(dAdqk_qt);
    }
    dAdqDescent.add(dAdq);
    dAdqDescent_dHdq.add(dAdq_H);
    dAdqDescent_dpdt.add(dAdq_qt);
    
    // filter gradient
    dAdq_filt = dAdq;
    //lowPassFiltering(dAdq_filt, false);
    //dAdqDescent_filt.add(dAdq_filt);
    cout << "dAdq size = " << dAdq.size() << endl;
   
    if (maxPrinting->boolValue())
    {
      debugfile << "-- dAdq_H --" << endl;
      debugfile << "[ ";
      for (int p=0; p<nPoints; p++)
      {
        debugfile << "(";
        StateVec dAdqk = dAdq_H.getUnchecked(p);
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

      debugfile << "-- dAdq_qt --" << endl;
      debugfile << "[ ";
      for (int p=0; p<nPoints; p++)
      {
        debugfile << "(";
        StateVec dAdqk = dAdq_qt.getUnchecked(p);
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

  // integrate hamilton equation of motion for current trajectory
  LOG("Verification using hamilton's equations of motion");
  hamiltonEoMVerification();
  
  // save descent algorithm results into a file
  LOG("writing descent to file");
  writeDescentToFile();
  
  //stop();
  
  
}















LiftResults NEP::nonLinearEquationSolving(const Curve& qcurve, int nls, bool maxPrintingAllowed, const int iteration)
{
  juce::Array<NLSresults> nlsResults;
  nlsResults.resize(nPoints-1);
  
  // dimension of the non-linear system
  const int n = simul->entities.size() + 1; // number of entities + 1


  int nThreads = juce::SystemStats::getNumCpus()-1;
  juce::ThreadPool pool(nThreads);

  // loop over points in concentration space
  // q : q0 -- p*_0 -- q1 -- p*_1 --  .. -- qi -- p*_i -- q(i+1) -- p*_(i+1) -- ...
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
    ev.dq_norm2 = norm2(deltaq);
    ev.epsilon = 1.;
    ev.n = n;
    // momentum normalization initialized to unity
    Array<double> pnorm;
    pnorm.insertMultiple(0, 1., n-1);
    ev.pnorm = pnorm;
    // equation normalization
    Array<double> eqnorm;
    eqnorm.insertMultiple(0, 1., n);
    ev.equation_norm = eqnorm;    

    jassert(ev.dq_norm2 > 0.);

    // verbose
    ev.maxPrintingAllowed = maxPrintingAllowed;
  
    // define v = dq / || dq ||
    StateVec v;
    for (int m=0; m<deltaq.size(); m++)
    {
      double vm = deltaq.getUnchecked(m) / ev.dq_norm2;
      v.add(vm);
    }
    ev.v = v;

    double dt_prev = 1.;
    StateVec pstar_prev;
    pstar_prev.insertMultiple(0, 0.1, n-1);
    // use results from previous iteration if succeeded
    //jassert(g_times.size() == nPoints-1);
    //jassert(g_pcurve.size() == nPoints-1);
    if (!justUpdatedSampling && g_times.size()==nPoints & g_pcurve.size() == nPoints) // #TODO add check on previous GSL status
    {
      dt_prev = g_times.getUnchecked(point+1) - g_times.getUnchecked(point);
      //jassert(pstar_prev.size() == g_pcurve.size());
      for (int m=0; m<g_pcurve.getUnchecked(point).size(); m++)
      {
        double pm_center = 0.5*(g_pcurve.getUnchecked(point).getUnchecked(m) + g_pcurve.getUnchecked(point+1).getUnchecked(m));
        pstar_prev.setUnchecked(m, pm_center);
      }
    }
    ev.dt_prev = dt_prev;
    ev.pstar_prev = pstar_prev;

    ev.iteration = iteration;
    
    pool.addJob(new NEPWorker(crn, ev, nlsResults.getReference(point), tolerance, nls, point, maxPrintingAllowed ,useChangeOfVariable->boolValue()), true);
  }

  

  // wait until job pool is empty
  while (pool.getNumJobs() > 0 && !threadShouldExit())
  {
    double jobFinished = 0.;
    for (int k=0; k<nPoints-1; k++)
    {
      if (nlsResults.getUnchecked(k).pstar.size() > 0.)
        jobFinished ++;
    }
    double percent = 100. * jobFinished / (double) (nPoints-1);
    std::cout << "\rProgress : " << percent << "%" << std::flush;
    sleep(1000);
  }
  std::cout << "\rProgress : " << 100 << "%" << std::endl;
  
  
  
  
  
  /*
   struct LiftResults
   {
       pCurve pcurve;
       juce::Array<double> times;
       juce::Array<double> residuals_H;
       juce::Array<juce::Array<double>> residuals_p;
   };
   
   struct NLSresults
   {
     int gslStatus;
     int collinearTest;
     double residual_H;
     juce::Array<double> residuals_p;
   };

   */
  
  // build global lifting results
  LiftResults output;
  for (auto & res : nlsResults)
  {
    output.dt.add(res.dt);
    output.pstar.add(res.pstar);
    output.gslStatus.add(res.gslStatus);
    output.collinearity.add(res.collinearTest);
    output.residuals_H.add(res.residual_H);
    output.residuals_p.add(res.residuals_p);
  }
  
  
   // add dummy values at the end so that output array sizes matches nPoints
   output.gslStatus.add(-999);
   output.collinearity.add(-999);
   output.residuals_H.add(-999.);
   StateVec dummy_residual_p;
   dummy_residual_p.insertMultiple(0, -999., simul->entities.size());
   output.residuals_p.add(dummy_residual_p);
   
   

  return output;
  
}

LiftResults NEP::liftCurveWithGSL(const Curve& qcurve, bool maxPrintingAllowed, const int iteration)
{
  
  
  
  //cout << "--- NEP::liftCurveWithGSL() ---" << endl;
  //cout << "input qcurve size = " << qcurve.size() << endl;
  
  
  // GSL to find optimal momentum and dt associated to qcurve
  LiftResults liftResults = nonLinearEquationSolving(qcurve, solverType->getValueDataAsEnum<int>(), maxPrintingAllowed, iteration);

  // measuring noise level in pstar and dt
  juce::Array<double> pstar_noise;
  double dt_noise = 0.;
  for (int i=0; i<simul->entities.size(); i++)
  {
    double noise = 0.;
    double max = 0.;
    for (int k=0; k<liftResults.pstar.size()-1; k++)
    {
      double pm = liftResults.pstar.getUnchecked(k).getUnchecked(i);
      double pm_next = liftResults.pstar.getUnchecked(k+1).getUnchecked(i);
      double pm_diff2 = (pm_next - pm)*(pm_next - pm);
      noise += pm_diff2;
      max = std::max(max, std::abs(pm));
    }
    noise /= (max * (double) (liftResults.pstar.size()-1));
    pstar_noise.add(noise);
  }
  if (maxPrintingAllowed)
  {
    //std::cout << "noise level in pstar : " << std::endl;
    //for (auto& el : pstar_noise)    
    //  std::cout << el << " ";
    //std::cout << std::endl;
  }

  
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
    for (auto & ppoint : liftResults.pstar)
    {
      debugfile << "(";
      int c=0;
      for (auto & pm : ppoint)
      {
        string closebracket = (p == liftResults.pstar.size()-1 ? ") " : "), ");
        string comma = ( c==ppoint.size()-1 ? closebracket : "," );
        debugfile << pm << comma;
        c++;
      }
      p++;
    }
  debugfile << " ]" << endl;
  debugfile << "dt = [ ";
  p=0;
  for (auto & tpoint : liftResults.dt)
  {
    string comma = (p == liftResults.dt.size()-1 ? "" : ", ");
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
    sumtime += liftResults.dt.getUnchecked(k-1);
    times.add(sumtime);
    
    // handle momentum, mean between current and next p
    if (k==nPoints-1) // force last momentum vec to be 0
      pcurve.add(nullP);
    else
    {
      StateVec meanP;
      for (int m=0; m<liftResults.pstar.getUnchecked(k).size(); m++)
      {
        double pm = 0.5*(liftResults.pstar.getUnchecked(k-1).getUnchecked(m) + liftResults.pstar.getUnchecked(k).getUnchecked(m));
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
    //jassert(avp.size() == n-1);
    av_pcurve.add(avp);
  }
  
  jassert(av_pcurve.size() == pcurve.size());
  double pmax = 0.;
  for (int k=0; k<pcurve.size(); k++)
  {
    StateVec pk = pcurve.getUnchecked(k);
    double norm_pk = norm2(pk);
    if (norm_pk > pmax)
      pmax = norm_pk;
  }
  jassert(pmax > 0.);

  // normalized distance between pcurve and av_pcurve
  double totdist = 0.;
  for (int k=0; k<pcurve.size(); k++)
  {
    StateVec pk = pcurve.getUnchecked(k);
    StateVec avpk = av_pcurve.getUnchecked(k);
    double dist = cartesianDistance(pk, avpk);
    totdist += dist;
  }
  totdist /= (pmax * (double) pcurve.size());
  if (maxPrintingAllowed)
  {
    //std::cout << "distance between pcurve and av_pcurve = " << totdist << endl;
  }
  //cout << "average pcurve size : " << av_pcurve.size() << endl;
  
   
  /*
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
  */
  
  /*
  // update global variables or not
  if (updateGlobalVar)
  {
    g_pcurve = pcurve;
    g_times = times;
  }
  */
  
  // Return optimization results
  //LiftResults output;
  //output.opt_deltaT = vec_dt;
  //output.opt_momentum = vec_pstar;
  //output.pcurve = pcurve;
  //output.times = times;
  
  liftResults.pcurve = pcurve;
  liftResults.smooth_pcurve = av_pcurve;
  liftResults.times = times;
  
  
  
  return liftResults;
  
}



void NEP::setTimeNormalizationFactor()
{
  //LOGWARNING("timescale always set to 1.");
  double tsfac = 1.;
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
    tsfac = 1. / meanK;
  }
  else
  {
    tsfac = 1.;
  }
  crn.timescale_factor = tsfac;
  nepsolver->setReactionNetwork(crn);
}




Curve NEP::deterministicInitialTrajectory(StateVec& qstable, StateVec& qsaddle, int sstI)
{
  Curve outcurve;

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


    int tries = 10;
    for (int tr=0; tr<tries; tr++)
    {
      // set first point of qcurve = qsaddle (unstable state)
      outcurve.clear();
      outcurve.add(qsaddle);

      RandomGausGenerator rg(0., 1.);
    
      // set initial concentration of entities to be very close from qF in the direction of qI
      Curve sl = {qstable, qsaddle};
      double L = curveLength(sl);
      jassert(L>0.);
      for (int i=0; i<qstable.size(); i++)
      {
        double di = 0.01*std::abs(qstable.getUnchecked(i)-qsaddle.getUnchecked(i)) / L;
        double ui = qsaddle.getUnchecked(i) + 0.01 * ( qstable.getUnchecked(i)-qsaddle.getUnchecked(i) ) / L;
        rg.shakeSeedValue();
        ui += rg.randomNumber() * std::sqrt(di);
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
        outcurve.add(qi);
      
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
    
      if (reachedSST != sstI && tr==tries-1)
      {
        LOGWARNING("System converged to steady state " + to_string(reachedSST) + " while steady state " + to_string(sstI) + " was specified.");
        throw std::runtime_error("Deterministic trajectory method failed to init. concentration trajectory. System did not converge to the correct steady state.");
      }
      else if (reachedSST == sstI)
      {
        // set last point of qcurve = qI
        outcurve.add(qstable);
        break;
      }
    
      
    }

    // reverse the direction of concentration curve
    std::reverse(outcurve.begin(), outcurve.end());
    
    // resample qcurve
    resampleInSpaceUniform(outcurve, nPoints);

    return outcurve;

}


Curve NEP::straightLineInitialTrajectory(StateVec& qstable, StateVec& qsaddle)
{
  Curve outcurve;
  double NN = (double) nPoints;
  for (int point=0; point<nPoints; point++)
    {
      StateVec vec;
      double fpoint = (double) point;
      for (int k=0; k<qstable.size(); k++)
      {
        double qk = qsaddle.getUnchecked(k) + (1. - fpoint/(NN-1.)) * (qstable.getUnchecked(k) - qsaddle.getUnchecked(k));
        vec.add(qk);
      }
      outcurve.add(vec);
    }
  return outcurve;
}


Curve NEP::guessInitialTrajectory(StateVec& qstable, StateVec& qsaddle, int sst_stable, int sst_saddle)
{
  SteadyState stable = simul->steadyStatesList->arraySteadyStates.getUnchecked(sst_stable);
  SteadyState saddle = simul->steadyStatesList->arraySteadyStates.getUnchecked(sst_saddle);

  cout << sst_stable << " , " << sst_saddle << endl;

  int index = -1;
  float lessNegative = 0.;
  cout << "stable has  Neigenvalues : " << stable.eigenvalues.size() << endl;
  for (int k=0; k<stable.eigenvalues.size(); k++)
  {
    auto& ev = stable.eigenvalues.getReference(k);
    cout << "ev.real = " << ev.real << endl;
    if (ev.real < lessNegative)
    {
      lessNegative = ev.real;
      index = k;
    }
  }
  if (index==-1)
  {
    throw std::runtime_error("Could not retrieve most likely escape direction from stable state. Exit.");
  }
  // retrieve eigenvector corresponding to most likely escape direction
  juce::Array<std::complex<float>> eigenvec = stable.eigenvectors.getUnchecked(index);
  StateVec dirStart;
  for (auto & c : eigenvec)
    dirStart.add(c.real());

  // saddle point
  index = -1;
  float lessPositive = 10000.;
  cout << "saddle has  Neigenvalues : " << saddle.eigenvalues.size() << endl;
  for (int k=0; k<saddle.eigenvalues.size(); k++)
  {
    auto& ev = saddle.eigenvalues.getReference(k);
    cout << "ev.real = " << ev.real << endl;
    if (ev.real < lessPositive && ev.real>0.)
    {
      lessPositive = ev.real;
      index = k;
    }
  }

  if (index==-1)
  {
    throw std::runtime_error("Could not retrieve most likely escape direction to saddle state. Exit.");
  }

  // retrieve eigenvector corresponding to most likely escape direction
  eigenvec = stable.eigenvectors.getReference(index);
  StateVec dirEnd;
  for (auto & c : eigenvec)
    dirEnd.add(c.real());

  StateVec stable2saddle;
  for (int k=0; k<qstable.size(); k++)
  {
    stable2saddle.add(qsaddle.getUnchecked(k)-qstable.getUnchecked(k));
  }

  double spstart = scalarProduct(dirStart, stable2saddle);
  if (std::abs(spstart)<1e-8)
  {
    throw std::runtime_error("Cannot initialize starting trajectory with guess method");
  }
  if (spstart < 0.) // reverse start direction
  {
    for (int k=0; k<dirStart.size(); k++)
      dirStart.setUnchecked(k, dirStart.getUnchecked(k)*-1.);
  }

  double spend = scalarProduct(dirEnd, stable2saddle);
  cout << "sp end = " << spend << endl;;
  cout << "v_saddle : ";
  for (auto & c : dirEnd)
    cout << c << " ";
  cout << endl;
  if (std::abs(spstart)<1e-8)
  {
    throw std::runtime_error("Cannot initialize ending trajectory with guess method");
  }
  if (spend > 0.) // reverse end direction
  {
    for (int k=0; k<dirEnd.size(); k++)
      dirEnd.setUnchecked(k, dirEnd.getUnchecked(k)*-1.);
  }

  cout << "v_saddle corrected : ";
  for (auto & c : dirEnd)
    cout << c << " ";
  cout << endl;


  double length = cartesianDistance(qstable, qsaddle);
  double step = 0.01;

  // curve escaping from stable point
  double l=0.;
  double lfac = 10.;
  Curve startCurve;
  startCurve.add(qstable);
  int c=0;
  while(l<length/lfac)
  {
    StateVec nextpoint;
    for (int k=0; k<qstable.size(); k++)
    {
      nextpoint.add(startCurve.getUnchecked(c).getUnchecked(k) + step*dirStart.getUnchecked(k));
    }
    startCurve.add(nextpoint);
    l += cartesianDistance(startCurve.getUnchecked(c+1), startCurve.getUnchecked(c));
    c++;
  }

  // curve going to saddle point
  l=0.;
  Curve endCurve;
  endCurve.add(qsaddle);
  c=0;
  while(l<length/lfac)
  {
    StateVec nextpoint;
    for (int k=0; k<qsaddle.size(); k++)
    {
      nextpoint.add(endCurve.getUnchecked(c).getUnchecked(k) + step*dirEnd.getUnchecked(k));
    }
    endCurve.add(nextpoint);
    l += cartesianDistance(endCurve.getUnchecked(c+1), endCurve.getUnchecked(c));
    c++;
  }
  // reverse points
  std::reverse(endCurve.begin(), endCurve.end());

  // join start and end segments.
  StateVec p1 = startCurve.getLast();
  StateVec p2 = endCurve.getFirst();
  Curve gap;
  int N = 100;
  double NN = (double) N;
  for (int i=0; i<N; i++)
  {
    double ii = (double) i;
    StateVec vec;
    for (int k=0; k<p1.size(); k++)
    {
      double qk = p2.getUnchecked(k) + (1. - ii/(NN-1.)) * (p1.getUnchecked(k) - p2.getUnchecked(k));
      vec.add(qk);
    }
    gap.add(vec);
  }

  // joining startCurve -- gap -- endCurve
  Curve totalCurve;
  for (auto & q : startCurve)
    totalCurve.add(q);
  for (auto & q : gap)
    totalCurve.add(q);
  for (auto & q : endCurve)
    totalCurve.add(q);

  // resample
  resampleInSpaceUniform(totalCurve, nPoints);

  return totalCurve;
  
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
  if (initialConditions->getValueDataAsEnum<int>() == 1)
  {
    g_qcurve = deterministicInitialTrajectory(qI, qF, sstI);
  }
  else if (initialConditions->getValueDataAsEnum<int>() == 0) // use straightline
  {
    g_qcurve = straightLineInitialTrajectory(qI, qF);
  }
  else if (initialConditions->getValueDataAsEnum<int>() == 2)
  {
    g_qcurve = guessInitialTrajectory(qI, qF, sstI, sstF);
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
  
  //std::ostringstream oss;
  //oss << std::scientific << std::setprecision(4) << tolerance_mu;
  //LOG("tolerance on H(p,q)=0 residual is : " + oss.str());
}


bool NEP::descentShouldUpdateParams(double diffAction)
{
  //cout << diffAction << " " << d_action_threshold << " || " << stepDescent << " " << d_stepDescentThreshold << endl;
  bool b1 = (diffAction<d_action_threshold || stepDescent<d_stepDescentThreshold);
  //bool b2 = nPoints < nPoints_max->intValue();
  return b1;
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
  int niters = trajDescent.size();
  system("mkdir -p descent");
  string filename = "descent/action-functionnal-descent_";
  filename += to_string(sst_stable->intValue()) + "-" + to_string(sst_saddle->intValue());
  filename += initialConditions->getValueDataAsEnum<int>()==0 ? "_straight-line-IC" : "_deterministic-IC";
  filename += "_" + to_string(nPointsUI->intValue()) + "points";
  filename += "_" + to_string(niters) + "iter";
  filename += ".csv";
  ofstream historyFile;
  historyFile.open(filename, ofstream::out | ofstream::trunc);
  
  historyFile << "Descent characteristics used :" << endl;
  historyFile << "Number of iterations : " << Niterations->intValue() << endl;
  historyFile << "Initial condition : " << initialConditions->getValueKey() << endl;
  historyFile << "Action threshold : " << action_threshold->stringValue() << endl;
  historyFile << "Timescale factor : " << crn.timescale_factor << endl;
  historyFile << "Initial step descent : " << stepDescentInitVal->floatValue() << endl;
  historyFile << "###############" << endl;
  
  historyFile << "iteration,point,gslStatus,collinearStatus,action,time";
  for (auto & ent : simul->entities)
    historyFile << ",q_" << ent->name;
  for (auto & ent : simul->entities)
    historyFile << ",p_" << ent->name;
  //for (auto & ent : simul->entities)
  //  historyFile << ",smooth_p_" << ent->name;
  //for (auto & ent : simul->entities)
  //  historyFile << ",dAdq_" << ent->name;
  //for (auto & ent : simul->entities)
  //  historyFile << ",dAdq_dHdq_" << ent->name;
  //for (auto & ent : simul->entities)
  //  historyFile << ",dAdq_dpdt_" << ent->name;
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
  //jassert(actionDescent.size() == smooth_pcurve_Descent.size());
  jassert(actionDescent.size() == timeDescent.size());
  jassert(actionDescent.size() == dAdqDescent.size());
  jassert(actionDescent.size() == dAdqDescent_dHdq.size());
  jassert(actionDescent.size() == dAdqDescent_dpdt.size());
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
      historyFile << "," << timeDescent.getUnchecked(iter).getUnchecked(point);
      PhaseSpaceVec trajpq = trajDescent.getUnchecked(iter).getUnchecked(point);
      StateVec dAdq_local = dAdqDescent.getUnchecked(iter).getUnchecked(point);
      StateVec dAdq_dHdq_local = dAdqDescent_dHdq.getUnchecked(iter).getUnchecked(point);
      StateVec dAdq_dpdt_local = dAdqDescent_dpdt.getUnchecked(iter).getUnchecked(point);
      //StateVec dAdq_filt_local = dAdqDescent_filt.getUnchecked(iter).getUnchecked(point);
      Array<double> resP = residuals_p_descent.getUnchecked(iter).getUnchecked(point);

      StateVec smoothp_local = smooth_pcurve_Descent.getUnchecked(iter).getUnchecked(point);
      
      jassert(resP.size() == simul->entities.size());
      if (resP.size() != simul->entities.size())
        cout << resP.size() << " " << simul->entities.size() << endl;
      
      //cout << "trajectory size : " << trajpq.size() << endl;
      for (int m=0; m<trajpq.size()/2; m++)
        historyFile << "," << trajpq.getUnchecked(m);
      for (int m=trajpq.size()/2; m<trajpq.size(); m++)
        historyFile << "," << trajpq.getUnchecked(m);
      //for (int m=0; m<smoothp_local.size(); m++)
      //  historyFile << "," << smoothp_local.getUnchecked(m);
      //for (int m=0; m<dAdq_local.size(); m++)
      //  historyFile << "," << dAdq_local.getUnchecked(m);
      //for (int m=0; m<dAdq_dHdq_local.size(); m++)
      //  historyFile << "," << dAdq_dHdq_local.getUnchecked(m);
      //for (int m=0; m<dAdq_dpdt_local.size(); m++)
      //  historyFile << "," << dAdq_dpdt_local.getUnchecked(m);
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
        double q = newqcurve.getUnchecked(k).getUnchecked(m) + step * dAdq.getUnchecked(k).getUnchecked(m);
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




//double NEP::backTrackingMethodForStepSize(const Curve& qc, const Curve& dAdq)
double NEP::backTrackingMethodForStepSize(const Curve& qc, LiftResults & _liftResults)
{
  // init step with previous value of stepDescent
  double step = stepDescentInit_dynamic;
  double minstep = 0.99*d_stepDescentThreshold;
  
  // timeout is such that minstep would be reached at last iteration
  int timeout = round(log(step/minstep) / log(2)) + 1;
  
  //cout << "NEP::backTrackingMethodForStepSize" << endl;
  
  Array<double> cumulaction = nepsolver->calculateAction(qc, g_pcurve, g_times);
  double currentaction = cumulaction.getLast();
  
  StateVec nullvec;
  nullvec.insertMultiple(0, 0., simul->entities.size());
  int count = 0;
 
  for (int iter=0; iter<timeout; iter++)
  {
    if (step<d_stepDescentThreshold)
    {
      break;
    }
    count++;
    
    //cout << "trying step = " << step << endl;
    
    // Try to update concentration curve with current step (returns false typically if concentrations would reach negative values)
    Curve newcurve = qc;
    bool updateIsValid = updateOptimalConcentrationCurve(newcurve, step);
    //cout << "update is Valid : " << updateIsValid << endl;
    
    if (!updateIsValid)
    {
      step *= 0.5;
      continue;
    }
    
    // find the corresponding lifted full trajectory, without updating global variables
    LiftResults liftResults = liftCurveWithGSL(newcurve, false, 0);
    
    
    // calculate action that would correspond to new concentration curve
    Array<double> newcumulaction = nepsolver->calculateAction(newcurve, liftResults.pcurve, liftResults.times);
    double newact = newcumulaction.getLast();
    //cout << "iter = " << iter << ". step = " << step << ". new action = " << newact << " vs current action = " << currentaction << endl;
    if (newact>=currentaction || newact<0.) // invalid step
    {
      step *= 0.5; // hardcoded (1/2)^17 = 7.6e-6, should be enough
    }
    else
    {
      //cout << "exiting loop" << endl;
      _liftResults = liftResults;
      break;
    }
  } // end backtracking loop 

  // if step is below threshold, set it to 0
  if (step<d_stepDescentThreshold)
    step = 0.;

  /*
  // if step too small, diminish start step value using current step value
  if (step<d_stepDescentThreshold || step<stepDescentInit_dynamic)
    stepDescentInit_dynamic = std::max(d_stepDescentThreshold*1.01, step);
  
  if (step == stepDescentInit_dynamic && adaptiveStepDescent->boolValue())
  {
    stepDescentInit_dynamic *= 2.;
  }
  */
  
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
    
    if (!break_forward)
      nepsolver->nextStepHamiltonEoM(qcurrent_forward, pcurrent_forward, qi, pi, dt, true, break_forward, traj_forward);
    if (!break_backward)
      nepsolver->nextStepHamiltonEoM(qcurrent_backward, pcurrent_backward, qi, pi, dt, false, break_backward, traj_backward);
    
  }
  
  pair<Trajectory, Trajectory> traj = make_pair(traj_forward, traj_backward); // one backward, one forward
  return traj;
}



void NEP::hamiltonEoMVerification()
{
  jassert(g_pcurve.size() == g_qcurve.size());
  if (g_pcurve.size() != g_qcurve.size())
  {
    LOGWARNING("q curve and p curve have different sizes. Cannot perform EoM verification");
    cout << "qcurve size : " << g_qcurve.size() << ". pcurve : " << g_pcurve.size() << endl;
  }

  juce::Array<pair<Trajectory, Trajectory>> hamiltonEoM;
  for (int point=1; point<g_qcurve.size()-1; point++) // skip first and last point = fixed points
  {
    StateVec q = g_qcurve.getUnchecked(point);
    StateVec p = g_pcurve.getUnchecked(point);

    pair<Trajectory, Trajectory> eom = integrateHamiltonEquations(q, p);
    hamiltonEoM.add(eom);
  }


  // write equation of motions to file
  std::system("mkdir -p ./hamilton-eq-of-motion");
  std::string file = "./hamilton-eq-of-motion/hamiltonsEoM.csv";
  std::ofstream eomfile;
  eomfile.open(file.c_str(), ofstream::out | ofstream::trunc);

  eomfile << "point,forward,step";
  for (auto & ent : simul->entities)
    eomfile << ",q_" << ent->name;
  for (auto & ent : simul->entities)
    eomfile << ",p_" << ent->name; 
  eomfile << std::endl;

  for (int point=0; point<hamiltonEoM.size(); point++)
  {
    Trajectory forward = hamiltonEoM.getUnchecked(point).first;
    Trajectory backward = hamiltonEoM.getUnchecked(point).second;

    // print forward trajectory
    for (int step=0; step<forward.size(); step++)
    {
      PhaseSpaceVec qp = forward.getUnchecked(step);
      eomfile << point+1 << "," << 1 << "," << step;
      for (auto & coord : qp)
        eomfile << "," << coord;
      eomfile << std::endl;
    }

    // print backward trajectory
    for (int step=0; step<backward.size(); step++)
    {
      PhaseSpaceVec qp = backward.getUnchecked(step);
      eomfile << point+1 << "," << 1 << "," << step;
      for (auto & coord : qp)
        eomfile << "," << coord;
      eomfile << std::endl;
    }


  } // end loop over points


}


void NEP::heteroclinicStudy()
{
  reset();

  // init concentration curve
  initConcentrationCurve();
  // lift it to full (q ; p) space
  //liftCurveToTrajectoryWithNLOPT_old();
  liftCurveWithGSL(g_qcurve, true, 0);
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
  buildReactionNetworkSnapshot();
  crn.timescale_factor = 1.;
  nepsolver->setReactionNetwork(crn);
  /*
  StateVec q = {1.58916000, 1.03974000};
  StateVec p = {0.01967720, 0.00082215};
  StateVec u = {std::exp(0.01967720), std::exp(0.00082215)};

// debug hamiltonian calculation in new variables

//double Hp = nepsolver->evalHamiltonian(q, p);
//double Hu = nepsolver->evalHamiltonian(q, u, true);

StateVec dHdp = nepsolver->evalHamiltonianGradientWithP(q, p);
StateVec uxdHdu = nepsolver->evalUtimesHamiltonianGradientWithU(q, u);
StateVec dHdu = nepsolver->evalHamiltonianGradientWithU(q, u);

juce::dsp::Matrix<double> hessp = nepsolver->evalHamiltonianHessianWithP(q, p);
juce::dsp::Matrix<double> hessu = nepsolver->evalHamiltonianHessianWithU(q, u);


cout << endl;
cout << "dH/dp = ";
for (auto& el : dHdp)
  cout << el << " ";
cout << endl << endl;

cout << "u x dH'/du [1] = ";
for (auto& el : uxdHdu)
  cout << el << " ";
cout << endl << endl;

cout << "u x dH'/du [2] = ";
for (int i=0; i<u.size(); i++)
  cout << u.getUnchecked(i) * dHdu.getUnchecked(i) << " ";
cout << endl << endl;

cout << "hess_p = " << endl;
for (int i=0; i<hessp.getNumRows(); i++)
{
  for (int j=0; j<hessp.getNumColumns(); j++)  
    cout << hessp(i, j) << " ";
  cout << endl;
}
cout << endl;

cout << "hess_u = " << endl;
for (int i=0; i<hessu.getNumRows(); i++)
{
  for (int j=0; j<hessu.getNumColumns(); j++)  
  {
    //double ij = hessu(i, j)*u.getUnchecked(j)*u.getUnchecked(i) + (i==j ? dHdu.getUnchecked(i)*u.getUnchecked(i) : 0.);
    double ij = hessu(i, j)*u.getUnchecked(j)*u.getUnchecked(i) + (i==j ? uxdHdu.getUnchecked(i) : 0.);
    cout << ij << " ";
  }
  cout << endl;
}
cout << endl;
*/


  /*
  StateVec qi = {0.5*(1.45199+1.4758), 0.5*(1.03513+1.03663)};
  StateVec pi = {0.0231699, 0.00159923};
  StateVec dq = {1.45199-1.4758, 1.03513-1.03663};
  double dq_norm2 = norm2(dq);
  StateVec v;
  for (int i=0; i<dq.size(); i++)
    v.add(dq.getUnchecked(i)/sqrt(dq_norm2));


  double n = 100;
  juce::Array<double> p1val; 
  for (int i=0; i<n; i++)
  {
    double ii = (double) i;
    p1val.add( 0.002 - (0.002-0.001)*ii/(n-1.) );
  }

  juce::Array<double> H;
  juce::Array<double> pv;

  for (int i=0; i<n; i++)
  {
    StateVec p = {0.0231699, p1val.getUnchecked(i)};
    double h = nepsolver->evalHamiltonian(qi, p);
    H.add(std::abs(h));
    double sp = scalarProduct(p, v);
    pv.add(sp);
  }

  cout << "p1 = [";
  for (int i=0; i<p1val.size(); i++)  {
    string comma = (i==p1val.size()-1 ? "]" : ", ");
    cout << p1val.getUnchecked(i) << comma;
  } 
  cout << endl;

  cout << "H = [";
  for (int i=0; i<H.size(); i++)  {
    string comma = (i==H.size()-1 ? "]" : ", ");
    cout << H.getUnchecked(i) << comma;
  } 
  cout << endl;

  cout << "p.v = [";
  for (int i=0; i<pv.size(); i++)  {
    string comma = (i==pv.size()-1 ? "]" : ", ");
    cout << pv.getUnchecked(i) << comma;
  } 
  cout << endl;
  */
  
  StateVec qi = {1.58889 ,  1.0429};
  StateVec pi = {0.0196599 ,  0.00116952};
  
  pair<Trajectory, Trajectory> eom = integrateHamiltonEquations(qi, pi);
  
  std::system("mkdir -p ./hamilton-eq-of-motion");
  
  ofstream output;
  output.open("./hamilton-eq-of-motion/hamilton-EoM_emergens.csv", ofstream::out | ofstream::trunc);
  
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