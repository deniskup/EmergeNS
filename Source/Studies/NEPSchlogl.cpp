#include "NEPSchlogl.h"
using namespace juce;





juce::Array<double> string2array(String str)
{
  juce::Array<double> keys;


  StringArray strarr;
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

  juce::Array<double> output;
  for (int i=0; i<n; i++)
  {
    double ii = static_cast<double>(i);
    double val = low + ii * (high - low) / (n - 1);
    output.add(val);
  }

  return output;
}






// constructor
NEPSchlogl::NEPSchlogl() : simul(Simulation::getInstance())
{
  if (simul == nullptr)
    LOGWARNING("SImulation pointer init. to null pointer");
}

// destructor
NEPSchlogl::~NEPSchlogl()
{
}






void NEPSchlogl::setConfig(std::map<String, String> configs)
{
  for (auto& [key, val] : configs)
  {
    //cout << "key, val : " << key << " " << val << endl;
    juce::var myvar(val);
 
  if (key == "iterations")
  {
    try
    {
        nIterations = std::atoi(val.toUTF8());
    }
    catch (const std::exception&)
    {
        initializationOK = false;
    }
  }
  else if (key == "points")
  {
    try
    {
        nPoints = std::atoi(val.toUTF8());
    }
    catch (const std::exception&)
    {
        initializationOK = false;
    }
  }
  else if (key == "theta")
  {
    theta = string2array(val);
  }
  else if (key == "kd")
  {
    kd = string2array(val);
  }
}

  for (auto & t: theta)
  {
    if (t < 0.)
    {
      initializationOK = false;
      LOGWARNING("Theta values must be positive. Please check config file.");
    }
  }
  for (auto & k: kd)
  {
    if (k < 0.)
    {
      initializationOK = false;
      LOGWARNING("Kd values must be positive. Please check config file.");
    }
  }
  
  // set some basic NEP configs
  NEP::getInstance()->Niterations->setValue(nIterations);
  NEP::getInstance()->useGradientDescentAscent->setValue(true);
  NEP::getInstance()->initialConditions->setValueAtIndex(3); 
  NEP::getInstance()->customInitialConditionFile->setValue("tempIC.csv");

  if (!initializationOK)
    LOGWARNING("Error in NEPSchlogl config file. Please check parameters.");


  // check
  cout << "theta = ";
  for (auto & t : theta)
    cout << t << " ";
  cout << endl;
  cout << "kd = ";
  for (auto & k : kd)
    cout << k << " ";
  cout << endl;


  // create pairs of [theta, kd]

  {
    const juce::ScopedLock sl(lock);
    thetakdpairs.clear();
    for (auto & t : theta)
    {
      for (auto & k : kd)
      {
        thetakdPair p;
        p.theta = t;
        p.kd = k;
        thetakdpairs.add(p);
      }
    }
  }

  cout << "thetakd pairs size = " << thetakdpairs.size() << endl;

}





void NEPSchlogl::startStudy()
{
  
  if (!initializationOK)
  {
    LOGWARNING("NEPSchlogl study not started due to config file errors.");
    return;
  }

  logerrorfile.open("NEPSchlogl_logs.txt", ios::out | ios::trunc);

  SteadyStateslist::getInstance()->addAsyncSteadyStateListener(this); // potentially dangerous if  steady states are computed independently 
  // from this study while it is still running
  // OK only assuming that this study is always running alone

  cout << "1st proceed to next theta KD pairs" << endl;
  proceedToNextThetaKd();
  
}





void NEPSchlogl::finishStudy()
{
  SteadyStateslist::getInstance()->removeAsyncSteadyStateListener(this);
}


void NEPSchlogl::updateThetaKd()
{
  
  if (thetakdpairs.size() == 0)
  {
    LOG("No more theta-kd pairs to study. NEPSchlogl study finished.");
    finishStudy();
    JUCEApplication::getInstance()->systemRequestedQuit();
    return;
  }
  
  // get first pair of theta and kd
  thetakdPair firstpair = thetakdpairs.getFirst();

  {
    const juce::ScopedLock sl(lock);
    thetakdpairs.remove(0);
  }

  // set entity inflows according to theta
  for (auto & se : simul->entities)
  {
    se->creationRate = firstpair.theta; 
    se->entity->creationRate->setValue(firstpair.theta);
  }

  // set diffusion reaction according to kd
  for (auto & sr : simul->reactions)
  {
    //cout << sr->reactants.size() << " " << sr->products.size() << endl;
    //cout << sr->reactants.getFirst()->name << " " << sr->products.getFirst()->name << endl;
    if (sr->reactants.size() == 1 && sr->products.size() == 1)
    {
      cout << "FOUND !" << endl;
      double barrier = -1.* std::log(firstpair.kd);
      sr->energy = barrier;
      sr->reaction->energy->setValue(barrier);
    }
  }

  current_theta = firstpair.theta;
  current_kd = firstpair.kd;

  cout << "theta, kd = " << current_theta << ", " << current_kd << endl;
  
}


void NEPSchlogl::requestSteadyStateCalculation()
{
  //SteadyStateslist::getInstance()->requestSteadyStateCalculation();
  simul->steadyStatesList->computeSteadyStates();
  //SteadyStateslist::getInstance()->computeSteadyStates();
}



void NEPSchlogl::proceedToNextThetaKd()
{
  // update theta and kd values
  cout << "updateThetaKd()" << endl;
  updateThetaKd();

  // request steady state calculation for current theta-kd pair
  cout << "requestSteadyStateCalculation()" << endl;
  requestSteadyStateCalculation();
}


bool NEPSchlogl::arrangeSteadyStates()
{
  // copy steady states from SteadyStateslist 
  stableSteadyStates.clear();
  saddleSteadyStates.clear();
  int c=-1;
  for (auto & ss : SteadyStateslist::getInstance()->getInstance()->arraySteadyStates)
  {
    c++;
    State state = ss.state;
    SchloglSteadyState ssst;
    ssst.X1 = state.getUnchecked(0).second; 
    ssst.X2 = state.getUnchecked(1).second; 
    ssst.stabilityOrder = ss.positiveEigenVal;
    ssst.positionInList = c;
    if (ssst.stabilityOrder == 0) // reject bi-saddle points
      stableSteadyStates.add(ssst);
    else if (ssst.stabilityOrder == 1) // reject bi-saddle points
      saddleSteadyStates.add(ssst);
  }

  // find symmetric steady states
  juce::Array<std::pair<int, int>> symmetricStablePairs;
  juce::Array<std::pair<int, int>> symmetricSaddlePairs;
  for (int i=0; i<stableSteadyStates.size(); i++)
  {
    for (int j=i+1; j<stableSteadyStates.size(); j++)
    {
      if (std::abs(stableSteadyStates[i].X1 - stableSteadyStates[j].X2) < 1e-4 &&
          std::abs(stableSteadyStates[i].X2 - stableSteadyStates[j].X1) < 1e-4)
      {
        symmetricStablePairs.add(std::make_pair(i, j));
      }
    }
  }
  for (int i=0; i<saddleSteadyStates.size(); i++)
  {
    for (int j=i+1; j<saddleSteadyStates.size(); j++)
    {
      if (std::abs(saddleSteadyStates[i].X1 - saddleSteadyStates[j].X2) < 1e-4 &&
          std::abs(saddleSteadyStates[i].X2 - saddleSteadyStates[j].X1) < 1e-4)
      {
        symmetricSaddlePairs.add(std::make_pair(i, j));
      }
    }
  }

  cout << "Stable steady states :" << endl;
  for (auto & ss : stableSteadyStates)
  {
    cout << "X1 = " << ss.X1 << ", X2 = " << ss.X2 << ", stability order = " << ss.stabilityOrder << endl;
  }
  cout << "Saddle steady states :" << endl;
  for (auto & ss : saddleSteadyStates)
  {
    cout << "X1 = " << ss.X1 << ", X2 = " << ss.X2 << ", stability order = " << ss.stabilityOrder << endl;
  } 
  
  // sanity check
  cout << "symmetric stable points : " << endl;
  for (auto& pair : symmetricStablePairs)
  {
    cout << pair.first << " " << pair.second << endl;
  }
  cout << "symmetric saddle points : " << endl;
  for (auto& pair : symmetricSaddlePairs)
  {
    cout << pair.first << " " << pair.second << endl;
  }

  // keep high X2 steady states
  juce::Array<SchloglSteadyState> trimmedStableSteadyStates;
  juce::Array<SchloglSteadyState> trimmedSaddleSteadyStates;
  for (auto & p : symmetricStablePairs)
  {
    if (stableSteadyStates[p.first].X2 > stableSteadyStates[p.second].X2)
    {
      trimmedStableSteadyStates.add(stableSteadyStates[p.first]);
    }
    else
    {
      trimmedStableSteadyStates.add(stableSteadyStates[p.second]);
    }
  }
  for (auto & p : symmetricSaddlePairs)
  {
    if (saddleSteadyStates[p.first].X2 > saddleSteadyStates[p.second].X2)
    {
      trimmedSaddleSteadyStates.add(saddleSteadyStates[p.first]);
    }
    else
    {
      trimmedSaddleSteadyStates.add(saddleSteadyStates[p.second]);
    }
  }


  cout << "Trimmed Stable steady states :" << endl;
  for (auto & ss : trimmedStableSteadyStates)
  {
    cout << "X1 = " << ss.X1 << ", X2 = " << ss.X2 << ", stability order = " << ss.stabilityOrder << endl;
  }
  cout << "Trimmed Saddle steady states :" << endl;
  for (auto & ss : trimmedSaddleSteadyStates)
  {
    cout << "X1 = " << ss.X1 << ", X2 = " << ss.X2 << ", stability order = " << ss.stabilityOrder << endl;
  } 

  stableSteadyStates = trimmedStableSteadyStates;
  saddleSteadyStates = trimmedSaddleSteadyStates;

  // sort steady states according to X1 + X2
  std::sort(stableSteadyStates.begin(), stableSteadyStates.end(), [](const SchloglSteadyState &a, const SchloglSteadyState &b) {
    return a.X1 + a.X2 < b.X1 + b.X2;
  });
  std::sort(saddleSteadyStates.begin(), saddleSteadyStates.end(), [](const SchloglSteadyState &a, const SchloglSteadyState &b) {
    return a.X1 + a.X2 < b.X1 + b.X2;
  });

  cout << "Trimmed and sorted Stable steady states :" << endl;
  for (auto & ss : stableSteadyStates)
  {
    cout << "X1 = " << ss.X1 << ", X2 = " << ss.X2 << ", stability order = " << ss.stabilityOrder << endl;
  }
  cout << "Trimmed and sorted Saddle steady states :" << endl;
  for (auto & ss : saddleSteadyStates)
  {
    cout << "X1 = " << ss.X1 << ", X2 = " <<  ss.X2 << ", stability order = " << ss.stabilityOrder << endl;
  }


  bool steadyStatesOK = true;
  if (stableSteadyStates.size() != 3)
  {
    steadyStatesOK = false;
    LOGWARNING("NEPSchlogl study : number of kept stable steady states is not equal to 3. Study will not be continued.");
  }
  if (saddleSteadyStates.size() != 2)
  {
    steadyStatesOK = false;
    LOGWARNING("NEPSchlogl study : number of kept saddle steady states is not equal to 2. Study will not be continued.");
  } 


  return steadyStatesOK;
  
}



void NEPSchlogl::writeCustomIC(const bool low2high)
{
  // write custom initial condition file for NEP
  std::ofstream icfile("tempIC.csv", std::ios::out | std::ios::trunc);
  if (!icfile.is_open())
  {
    LOGWARNING("Could not open tempIC.csv for writing. NEP study will not be continued.");
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

void NEPSchlogl::launchOneGDA()
{

  // set start SST and endSST of NEP according to results of steady state calculation
  // do not throw NEP if less than 4 stable steady states are found
  // set initial trajectory accordingly
  bool canContinue = arrangeSteadyStates();

  // find a way to pass an outputfile name to NEP
  if (canContinue)
  {
    for (int k=0; k<2; k++)
    {
      bool low2high = (k == 0) ? true : false;
      int start = low2high ? 0 : 2;
      int end = low2high ? 2 : 0;
      
      NEP::getInstance()->sst_stable->setValue(stableSteadyStates[start].positionInList);
      NEP::getInstance()->sst_stable2->setValue(stableSteadyStates[end].positionInList);

      writeCustomIC(low2high);

      // launch one gradient descent ascent
      //NEP::getInstance()->startDescent->trigger();
    }
  }
  else
  {
    logerrorfile << "Steady states issue for theta = " << current_theta << ", kd = " << current_kd;
    logerrorfile << "trimmed stable steady states = " << stableSteadyStates.size() << ", ";
    logerrorfile << "trimmed saddle steady states = " << saddleSteadyStates.size() << endl;

    // proceed manually to next theta-kd pair
    proceedToNextThetaKd();
  }

  
  
}


void NEPSchlogl::newMessage(const NEP::NEPEvent &ev)
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
      logerrorfile << "Error in gradient descent ascent for theta = " << current_theta << ", kd = " << current_kd << endl; 
      proceedToNextThetaKd();   
    }
  break;
      
    case NEP::NEPEvent::FINISHED:
    {
      // update theta and kd values
      proceedToNextThetaKd();
    }
  break;
      
  } // end switch
}




void NEPSchlogl::newMessage(const SteadyStateslist::SteadyStateEvent &ev)
{
  
  switch (ev.type)
  {   
    case SteadyStateslist::SteadyStateEvent::WILL_START:
    {
      cout << "Message Will start steady state calculation received" << endl;
    }
  break;
      
    case SteadyStateslist::SteadyStateEvent::FINISHED:
    {
      // launch next gradient descent ascent
      cout << "SST finished, launch one GDA" << endl;
      launchOneGDA();
    }
  break;
      
  } // end switch
}
