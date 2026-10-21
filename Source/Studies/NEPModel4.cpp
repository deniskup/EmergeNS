#include "NEPModel4.h"
using namespace juce;











// constructor
NEPModel4::NEPModel4() : simul(Simulation::getInstance())
{
  if (simul == nullptr)
    LOGWARNING("SImulation pointer init. to null pointer");
}

// destructor
NEPModel4::~NEPModel4()
{
}




juce::Array<double> NEPModel4::string2array(juce::String str)
{
 
  juce::Array<double> output;

  if (str.contains(";"))
  {
     juce::Array<double> keys;
    juce::StringArray strarr;
    strarr.addTokens(str, ";", "");
    for (auto & s : strarr)
    {
      keys.add(atof(s.toUTF8()));
    }
    if (keys.size() != 3)
    {
      throw std::runtime_error("Array must have exactly 3 elements.");
    }

    double low = keys[0];
    double high = keys[1];
    int n = static_cast<int>(keys[2]);
    if (n < 2)
    {
      throw std::runtime_error("Number of points must be at least 2.");
    }

    
    for (int i=0; i<n; i++)
    {
      double ii = static_cast<double>(i);
      double val = low + ii * (high - low) / (n - 1);
      output.add(val);
   }
  }
  else
  {
    juce::StringArray strarr;
    strarr.addTokens(str, ",", "");
    for (auto & s : strarr)
    {
      output.add(atof(s.toUTF8()));
    }
  }

  return output;
}






void NEPModel4::setConfig(std::map<String, String> configs)
{
  for (auto& [key, val] : configs)
  {
    //cout << "key, val : " << key << " " << val << endl;
    if (val == "")
    {
      //cout << "ignoring key " << key << " as val is null" << endl;
      continue;
    }
    if (key.trimStart().startsWith("#"))
    {
      //cout << "ignoring key " << key << endl;
      continue;
    }

    juce::var myvar(val);
 
  if (key == "iterations")
  {
    try
    {
        nIterations = std::atoi(val.toUTF8());
    }
    catch (const std::exception&)
    {
        LOGWARNING("iteration key value format incorrect. Please check config file");
        initializationOK = false;
    }
  }
  if (key == "studyType")
  {
    if (val == "steadyStates")
      studytype = STEADYSTATES; 
    else if (val == "NEP1PATCH")
      studytype = NEP1PATCH;
  }
  else if (key == "points")
  {
    try
    {
        nPoints = std::atoi(val.toUTF8());
    }
    catch (const std::exception&)
    {
        LOGWARNING("nPoints key value format incorrect. Please check config file");
        initializationOK = false;
    }
  }
  else if (key == "deltaG")
  {
    deltaG = string2array(val);
  }
  else if (key == "detectConvergence")
  {
    int ival;
    try
    {
      ival = std::atoi(val.toUTF8());
    }
    catch (const std::exception&)
    {
      LOGWARNING("detectConvergence key value format incorrect. Please check config file");
      initializationOK = false;
    }
    detectConvergence = (ival != 0);
  }
  else if (key == "checkpoints")
  {
    try
    {
      checkpoints = std::atoi(val.toUTF8());
    }
    catch (const std::exception&)
    {
      LOGWARNING("checkpoints key value format incorrect. Please check config file");
      initializationOK = false;
    }
  }
  else if (key == "barrier")
  {
    barr = string2array(val);
  }
  else if (key == "dtau")
  {
    try
    {
        dtau = std::atof(val.toUTF8());
    }
    catch (const std::exception&)
    {
      LOGWARNING("dtau key value format incorrect. Please check config file");
      initializationOK = false;
    }
  }
  else if (key == "alpha")
  {
    try
    {
        alpha = std::atof(val.toUTF8());
    }
    catch (const std::exception&)
    {
      LOGWARNING("alpha key value format incorrect. Please check config file");
      initializationOK = false;
    }
  }
  else if (key == "actionThreshold")
  {
    try
    {
        action_threshold = std::atof(val.toUTF8());
    }
    catch (const std::exception&)
    {
      LOGWARNING("actionThreshold key value format incorrect. Please check config file");
      initializationOK = false;
    }
  }
  else if (key == "outputdir")
  {
    outputdir = val.toStdString();   
  }
  else if (key == "msolvePath")
  {
    msolvePath = val;   
  }
  else if (key == "dGbarrFile")
  {
    file_pairs_dGbarr = val;   
  }
}

  for (auto & b: barr)
  {
    if (b < 0.)
    {
      initializationOK = false;
      LOGWARNING("Barriers values must be positive. Please check config file.");
    }
  }

  
  // set some basic NEP configs
  NEP::getInstance()->Niterations->setValue(nIterations);
  NEP::getInstance()->nPointsUI->setValue(nPoints);
  NEP::getInstance()->useGradientDescentAscent->setValue(true);
  NEP::getInstance()->customInitialConditionFile->setValue("tempIC.csv");
  NEP::getInstance()->dtau->setValue(dtau);
  NEP::getInstance()->alpha->setValue(alpha);
  NEP::getInstance()->GDAdetectConvergence->setValue(detectConvergence);
  NEP::getInstance()->GDAcheckpoints->setValue(checkpoints);
  Settings::getInstance()->pathToMSolve->setValue(msolvePath);

  if (studytype == NEP1PATCH)
    NEP::getInstance()->initialConditions->setValueAtIndex(0);  // straightline
  //else if (studytype == NEP2PATCH)
  //  NEP::getInstance()->initialConditions->setValueAtIndex(3); 


  if (!initializationOK)
    LOGWARNING("Error in NEPModel4 config file. Please check parameters.");



  // create pairs of [barrier, deltaG]
  {
    const juce::ScopedLock sl(lock);
    dGbarrpairs.clear();
    if (file_pairs_dGbarr == "")
    {
      for (auto & dg  : deltaG)
      {
        for (auto & b : barr)
        {
          ThermoKinPair p;
          p.deltaG = dg;
          p.barr = b;
          dGbarrpairs.add(p);
        }
      }
    }
    else
    {
      initdGBarrPairsFromCSV();
    }
  }
  

  simID = 0;
  fromA2B = true;
  nepHasError = false;

  if (studytype == NONE)
  {
    LOGWARNING("Study type not recognized");
    initializationOK = false;
  }

  // set matrix cycle
  cycleMatrix.resize(3,3);
  cycleMatrix(0,0) = -1.;
  cycleMatrix(0,1) = 0.;
  cycleMatrix(0,2) = 1.;
  cycleMatrix(1,0) = 0.;
  cycleMatrix(1,1) = 1.;
  cycleMatrix(1,2) = -1.;
  cycleMatrix(2,0) = 2.;
  cycleMatrix(2,1) = -1.;
  cycleMatrix(2,2) = 0.;

  steadyStates.clear();

  metadatafile  = outputdir + "/metadata.csv";
  logfilename  = outputdir + "/log-error.txt";

  // snaity check
  //for (auto &p : dGbarrpairs)
 // {
  //  cout << "dG = " << p.deltaG << ". barrier = " << p.barr << endl;
  //}

}


void NEPModel4::initdGBarrPairsFromCSV()
{
  // read input file
  ifstream f;
  f.open(file_pairs_dGbarr.toUTF8());
  if (!f.is_open())
  {
    LOGWARNING("Cannot open file " + file_pairs_dGbarr);
    initializationOK = false;
  }

  //std::vector<std::string>   result;

  // index of barrier, 0 or 1
  int ibarr = -1;

  // read first line and 'spot which column is barrier and which is deltaG
  std::string line;
  std::getline(f,line);
  //cout << "first line :\n" << line << endl;
  std::stringstream          lineStream(line);
  std::string                cell;

  int c=0;
  while(std::getline(lineStream,cell, ','))
  {
    //result.push_back(cell);
    //cout << cell << endl;
    if (cell == "barrier")
      ibarr = c;
    c++;
  }

  if (c != 2)
  {
    LOGWARNING("More than two columns in barrier-deltaG input csv file. Please check.");
    initializationOK = false;
    return;
  }
  if (ibarr == -1)
  {
    LOGWARNING("One of the columns of input barrier-deltaG file must be labeled 'barrier'. Please check.");
    initializationOK = false;
    return;
  }

  // idelta G value
  int ideltaG = (ibarr == 0) ? 1 : 0;

  // read rest of the file
  c = 0;
  //cout << "reste of the file" << endl;
  while(std::getline(f,line))
  {
    //cout << line << endl;
    lineStream.str(line);
    lineStream.clear();
    ThermoKinPair pair;
    int c2 = 0;
    while(std::getline(lineStream,cell, ','))
    {
      //result.push_back(cell);
      //cout << c2 << endl;
      if (c2 == ibarr)
      {
        double val;
        try
        {
          val = std::atof(cell.c_str());
        }
        catch (const std::exception&) // i practive atof is pretty convenient with bad formmated string
        // 0.2t3 will become 0.2 in spite of the typo, so most of what I want to catch here
        // will not be. Should rather check string validity with home-made function
        // is_valid_float(cell)
        // and request that cell contains only digitis and '.'
        {
          LOGWARNING("Input csv file error float format at line " + String(c+2));
          initializationOK = false;
          break;
        }
        pair.barr = val;
      }
      else if (c2 == ideltaG)
      {
        double val;
        try
        {
          val = std::atof(cell.c_str());
        }
        catch (const std::exception&)
        {
          LOGWARNING("Input csv file error float format at line " + String(c+2));
          initializationOK = false;
          break;
        }
        pair.deltaG = val;
      }
      else
      {
        LOGWARNING("Input csv file error float format at line " + String(c+2));
        initializationOK = false;
        break;
      }
      c2++;
    }
    dGbarrpairs.add(pair);
    c++;
  }
   
  // check
  /*cout << "barr-dG pairs: " << endl;
  for (auto & p : dGbarrpairs)
  {
    cout << p.barr << "\t" << p.deltaG << endl;
  }*/

    //initializationOK = false;
}






void NEPModel4::startStudy()
{
  
  if (!initializationOK)
  {
    LOGWARNING("NEPModel4 study not started due to config file errors.");
    return;
  }

  logerrorfile.open(logfilename.c_str(), ios::out | ios::trunc);
  ofs_metadata.open(metadatafile.c_str(), ios::out | ios::trunc);

  if (studytype == STEADYSTATES)
  {
    ofs_metadata << "simID,deltaG,barr" << endl;
  }
  else
  {
    ofs_metadata << "simID,deltaG,barr,fromA2B,filename,steadyStatesOK,nepOK" << endl;
  }
  ofs_metadata.close();
  logerrorfile.close();

  // make this class listen to NEP and SteadyState instances
  //simul->steadyStatesList->addAsyncSteadyStateListener(this);
  simul->addAsyncSimulationListener(this);
  NEP::getInstance()->addAsyncNEPListener(this);

  proceedToNext_dGbarr();
}





void NEPModel4::finishStudy()
{
  //simul->steadyStatesList->removeAsyncSteadyStateListener(this);
  if (studytype == STEADYSTATES)
    saveSteadyStatesToFile();
  simul->removeAsyncSimulationListener(this);
  NEP::getInstance()->removeAsyncNEPListener(this);
}


void NEPModel4::update_dGbarr()
{
  
  if (dGbarrpairs.size() == 0)
  {
    LOG("No more deltaG_barrier pair to study. NEPModel4 study finished.");
    finishStudy();
    JUCEApplication::getInstance()->systemRequestedQuit();
    return;
  }
  
  // get first pair of theta and kd
  ThermoKinPair firstpair = dGbarrpairs.getFirst();
  {
    const juce::ScopedLock sl(lock);
    dGbarrpairs.remove(0);
  }


  // solve for free energies of cycle B
  CycleFreeEnergies fE = solveFreeEnergies(firstpair.deltaG);

  // assign free energies to entities
  for (auto & se : simul->entities)
  {
    if (se->name == "B2" || se->name == "AB2")
    {
      //se->freeEnergy = fE.e2;
      se->entity->freeEnergy->setValue(fE.e2);
      //cout << "updating " << se->name << " : " << fE.e2 <<  endl;
    }
    else if (se->name == "B4")
    {
      se->entity->freeEnergy->setValue(fE.e4);
      //se->freeEnergy = fE.e4;
      //cout << "updating " << se->name << " : " << fE.e4 <<  endl;
    }
    else if (se->name == "B5")
    {
      se->entity->freeEnergy->setValue(fE.e5);
      //se->freeEnergy = fE.e5;
      //cout << "updating " << se->name << " : " << fE.e5 <<  endl;
    }
  }

  // set reaction barriers of cycle B
  for (auto & sr : simul->reactions)
  {
    bool ok = false;
    // look for B entities in reactants
    for (auto & se : sr->reactants)
    {
      if (se->name == "B5" || se->name == "B4")
      {
        ok = true;
        break;
      }
    }
    // same for products
    for (auto & se : sr->products)
    {
      if (se->name == "B5" || se->name == "B4")
      {
        ok = true;
        break;
      }
    }
    if (ok)
      sr->reaction->energy->setValue(firstpair.barr);
  
      //sr->energy = firstpair.barr;
  }
  current_dg = firstpair.deltaG;
  current_barr = firstpair.barr;

  
}




CycleFreeEnergies NEPModel4::solveFreeEnergies(const double& dg)
{
  Eigen::Vector3d B(dg, dg, dg);
  Eigen::Vector3d X = cycleMatrix.colPivHouseholderQr().solve(B);

  CycleFreeEnergies fe;
  fe.e2 = X(0);
  fe.e4 = X(1);
  fe.e5 = X(2);

  //cout << "Free energies : " << X << endl;

  return fe;
}


void NEPModel4::requestSteadyStateCalculation()
{
  simul->steadyStatesList->computeSteadyStates();
}



void NEPModel4::proceedToNext_dGbarr()
{
  if (studytype == STEADYSTATES)
  {
    // update barrier and deltaG values
    update_dGbarr();

    // request steady state calculation for current theta-kd pair
    requestSteadyStateCalculation();
  }
  else if (studytype == NEP1PATCH)
  {
    if (fromA2B)
    {
      // next value of deltaG and barrier
      update_dGbarr();

      // request steady state calculation for current theta-kd pair
      requestSteadyStateCalculation();
    }
    else
    {
      launchOneGDA();
    }
  }
}


std::pair<int, int> NEPModel4::arrangeSteadyStates(bool & canContinue)
{
  // check bistability
  int nStable = 0;
  for (auto & sst : simul->steadyStatesList->arraySteadyStates)
  {
    if (sst.isStable)
      nStable ++;
  }

   // find steady states dominated by A cycle and B cycle.
  int Adominates = -1;
  int Bdominates = -1;


   if (nStable != 2)
  {
    canContinue = false;
    return std::pair<int, int>(Adominates, Bdominates);
  }

  for (int i=0; i<simul->steadyStatesList->arraySteadyStates.size(); i++)
  {
    SteadyState sst = simul->steadyStatesList->arraySteadyStates.getUnchecked(i);
    if (!sst.isStable)
      continue;
    double abund_Acycle = 0.;
    double abund_Bcycle = 0.;
    for (auto & pair : sst.state)
    {
      if (pair.first->name == "A2" || pair.first->name == "A5" || pair.first->name == "A5")
        abund_Acycle += pair.second;
      if (pair.first->name == "B2" || pair.first->name == "B5" || pair.first->name == "B5")
        abund_Bcycle += pair.second;
    }

    if (abund_Acycle > abund_Bcycle)
      Adominates = i;
    if (abund_Acycle < abund_Bcycle)
      Bdominates = i;
  }

  if (Adominates == -1 || Bdominates == -1)
  {
    canContinue = false;
    return std::pair<int, int>(Adominates, Bdominates);
  }
  
  cout << "A dominates = " << Adominates << endl;
  cout << "B dominates = " << Bdominates << endl;

  return std::pair<int, int>(Adominates, Bdominates);
  
}



/*void NEPModel4::writeCustomIC(const bool low2high)
{
  // write custom initial condition file for NEP
  std::ofstream icfile("tempIC.csv", std::ios::out | std::ios::trunc);
  if (!icfile.is_open())
  {
    LOGWARNING("Could not open tempIC.csv for writing. NEP study will not be continued.");
    updateInternalParameters();
    proceedToNextThetaKd();
    return;
  }

  // write header
  for (auto & se : simul->entities)
  {
    icfile << se->name << ",";
  }
  for (int i=0; i<simul->entities.size(); i++)
  {
    string comma = (i == simul->entities.size() - 1) ? "" : ",";
    icfile << "p_" << simul->entities.getUnchecked(i)->name << comma;
  }
  icfile << std::endl;


  // normally this case should already be avoided by the arrangeSteadyStates() function, but we check again
  // in order to avoid seg faults here
  if (stableSteadyStates.size() != 3 || saddleSteadyStates.size() != 2)
  {
    LOGWARNING("NEPSchlogl study : number of kept stable steady states is not equal to 3 or number of kept saddle steady states is not equal to 2. Study will not be continued.");
    icfile.close();
    updateInternalParameters();
    proceedToNextThetaKd();
    return;
  }

  // write initial condition as stable1 --> saddle1 --> saddle2 --> stable3
  if (low2high)
  {
    icfile << stableSteadyStates[0].X1 << "," << stableSteadyStates[0].X2 << ",0.,0." << std::endl;
    icfile << saddleSteadyStates[0].X1 << "," << saddleSteadyStates[0].X2 << ",0.,0." << std::endl;
    icfile << saddleSteadyStates[1].X1 << "," << saddleSteadyStates[1].X2 << ",0.,0." << std::endl;
    icfile << stableSteadyStates[2].X1 << "," << stableSteadyStates[2].X2 << ",0.,0." << std::endl;
  }
  else
  {
    icfile << stableSteadyStates[2].X1 << "," << stableSteadyStates[2].X2 << ",0.,0." << std::endl;
    icfile << saddleSteadyStates[1].X1 << "," << saddleSteadyStates[1].X2 << ",0.,0." << std::endl;
    icfile << saddleSteadyStates[0].X1 << "," << saddleSteadyStates[0].X2 << ",0.,0." << std::endl;
    icfile << stableSteadyStates[0].X1 << "," << stableSteadyStates[0].X2 << ",0.,0." << std::endl;
  }

  icfile.close();
}
*/

void NEPModel4::launchOneGDA()
{

  // set start SST and endSST of NEP according to results of steady state calculation
  // do not throw NEP if less than 4 stable steady states are found
  // set initial trajectory accordingly
  bool canContinue = true;
  pair<int, int> cycle_index = arrangeSteadyStates(canContinue);

  // find a way to pass an outputfile name to NEP
  if (canContinue)
  {
      int Acycle_index = cycle_index.first;
      int Bcycle_index = cycle_index.second;

      int start, end;
      start = fromA2B ? Acycle_index : Bcycle_index;
      end = fromA2B ? Bcycle_index : Acycle_index;
      
      NEP::getInstance()->sst_stable->setValue(start);
      NEP::getInstance()->sst_stable2->setValue(end);

      cout << "startSST --> endSST = " << start;
      cout << " --> " << end << endl;

      //writeCustomIC(low2high);

      // outputfile filename
      //outputfile = "./gda/simID-" + to_string(simID) + "_theta_" + to_string(current_theta) + "_kd_" + to_string(current_kd) + (low2high ? "_low-high" : "_high-low") + ".csv";
      outputfile = outputdir + "/simID-" + to_string(simID) + "_barr_" + to_string(current_barr) 
      + "_dG_" + to_string(current_dg) + (fromA2B ? "_A-B" : "_B-A") + ".csv";
      NEP::getInstance()->setCustomOutputFilename(outputfile);

      // launch one gradient descent ascent
      NEP::getInstance()->startDescent->trigger();
      
  }
  else
  {
    logerrorfile << "Steady states issue for barrier = " << current_barr << ", deltaG = " << current_dg;


    saveToMetadata(false);

    // proceed manually to next theta-kd pair
    updateInternalParameters();
    proceedToNext_dGbarr();
  }
  
}



void NEPModel4::retrieveSteadyStates()
{
  for (auto & sst : simul->steadyStatesList->arraySteadyStates)
  {
    if (sst.isStable)
    {
      SteadyState copySST(sst);
      Model4SteadyState m4sst;
      m4sst.steadyState = copySST;
      m4sst.barr = current_barr;
      m4sst.deltaG = current_dg;
      m4sst.simID = simID;
      steadyStates.add(m4sst);
    }
  }

}


void NEPModel4::saveToMetadata(const bool & steadyStateOK)
{
  std::string completename = outputdir + "/metadata.csv";
  ofs_metadata.open(completename.c_str(), ios::ate | ios::app);

  if (!ofs_metadata.is_open())
    return;

  if (studytype == STEADYSTATES)
  {
    ofs_metadata << simID << "," << current_dg << "," << current_barr << endl;
  }
  else
  {
    ofs_metadata << simID << "," << current_dg << "," << current_barr << "," << fromA2B;
    ofs_metadata << "," << outputfile << "," << steadyStateOK << "," << !nepHasError << endl;
  }
  
  ofs_metadata.close();
}



void NEPModel4::saveSteadyStatesToFile()
{
  ofstream out;
  outputfile = outputdir + "/steadyStates.csv";
  out.open(outputfile, ios::trunc | ios::out);

  // 1st line
  out << "simID,deltaG,barrier";
  for (auto & se : simul->entities)
  {
    out << "," << se->name;
  }
  out << std::endl;


  for (auto & m4sst : steadyStates)
  {
    out << m4sst.simID << "," << m4sst.deltaG << "," << m4sst.barr;
    for (auto & p : m4sst.steadyState.state)
      out << "," << p.second;
    out << std::endl;
  }


}


void NEPModel4::updateInternalParameters()
{
  simID++;
  fromA2B = !fromA2B;
  nepHasError = false;
}


void NEPModel4::newMessage(const NEP::NEPEvent &ev)
{
  
  switch (ev.type)
  {   
    case NEP::NEPEvent::WILL_START:
    {
      
    }
  break;

    case NEP::NEPEvent::NEWSTEP:
    {
    }
  break;

    case NEP::NEPEvent::ERROR:
    {  
      string s = fromA2B ? ". Mode A --> B" : "A";
      logerrorfile << "Error in gradient descent ascent for barrier = " << current_barr << ", deltaG = " << current_dg << s << endl; 
      nepHasError = true;
    }
  break;
      
    case NEP::NEPEvent::FINISHED:
    {
      //cout << "received NEPEvent::FINISHED" << endl;
      // record metadata
      saveToMetadata(true);

      // update relevant parameters
      updateInternalParameters();

      // update theta and kd values
      proceedToNext_dGbarr();
    }
  break;
      
  } // end switch
}



void NEPModel4::newMessage(const Simulation::SimulationEvent &ev)
{
	switch (ev.type)
	{
	case Simulation::SimulationEvent::UPDATEPARAMS:
	{
		// launch next gradient descent ascent
    if (studytype == STEADYSTATES)
    {
      retrieveSteadyStates();
      saveToMetadata(true);
      updateInternalParameters();
      proceedToNext_dGbarr();
    }
    else if (studytype == NEP1PATCH)
    {
      launchOneGDA();
    }
	}
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

	case Simulation::SimulationEvent::NEWGILLESPIE_STEP:
	{
	}
	break;

	case Simulation::SimulationEvent::NEWRUN:
	{
	}
	break;

	case Simulation::SimulationEvent::FINISHED:
	{
	}

	} // end switch
}



/*
void NEPModel4::newMessage(const SteadyStateslist::SteadyStateEvent &ev)
{
  
  switch (ev.type)
  {   
    case SteadyStateslist::SteadyStateEvent::WILL_START:
    {
    }
  break;
      
    case SteadyStateslist::SteadyStateEvent::FINISHED:
    {
      // launch next gradient descent ascent
      launchOneGDA();
    }
  break;
      
  } // end switch
}
*/