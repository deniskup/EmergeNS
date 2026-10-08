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
    ```cpp
  if (key == "network")
  {
    network = val;
  }
  else if (key == "iterations")
  {
    try
    {
        nIterations = std::stoi(val.toUTF8());
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
        nPoints = std::stoi(val.toUTF8());
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

  SteadyStateslist::getInstance()->addListener(this); // potentially dangerous if  steady states are computed independently 
  // from this study while it is still running
  // OK only assuming that this study is always running alone

  // update theta, kd in Simulation
  updateThetaKd();

  // request steady state calculation for current theta-kd pair
  requestSteadyStateCalculation();
  
}





void NEPSchlogl::finishStudy()
{
  SteadyStateslist::getInstance()->removeListener(this);
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
    se->inflow->setValue(firstpair.theta); 
  }

  // set diffusion reaction according to kd
  for (auto & sr : simul->reactions)
  {
    if (sr->reactants.size() == 1 && sr->products.size() == 1 && sr->reactants.getFirst()->name == sr->products.getFirst()->name)
    {
      double barrier = -1.* std::log(firstpair.kd);
      sr->energy = barrier;
    }
  }
  
}


void NEPSchlogl::requestSteadyStateCalculation()
{
  SteadyStateslist::getInstance()->requestSteadyStateCalculation();
}




void NEPSchlogl::launchOneGDA()
{

  // set start SST and endSST of NEP according to results of steady state calculation
  // do not throw NEP if less than 4 stable steady states are found
  // set initial trajectory accordingly

  // find a way to pass an outputfile name to NEP

  // launch one gradient descent ascent
  NEP::getInstance()->startDescent->trigger();
  
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
    }
  break;
      
    case NEP::NEPEvent::FINISHED:
    {
      // update theta and kd values
      updateThetaKd();
      requestSteadyStateCalculation();
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
