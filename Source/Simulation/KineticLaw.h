/*
  ==============================================================================

  KineticLaw.h
  Created: 09 Feb 2026
  Author:  thkosc

  ==============================================================================
*/

#pragma once
#include <JuceHeader.h>
#include "SimEntity.h"
#include "SimReaction.h"
#include "Space.h"
using namespace juce;
using namespace std;


class RandomGausGenerator
{
  public:
  RandomGausGenerator(float _mu, float _sigma) // constructor
  {
    mu = _mu;
    sigma = _sigma;
    gausDist = new normal_distribution<float>;
    normal_distribution<float> dtemp(mu, sigma);
    gausDist->param(dtemp.param());
    generator=new default_random_engine;
  };
  
  // attributes
  default_random_engine * generator;
  normal_distribution<float> * gausDist;
  float mu = 0.;
  float sigma = 1.;
  //unsined long seed;
  
  // generate actual random number
  float randomNumber()
  {
    return (*gausDist)(*generator);
  }
  
  void setFixedSeed(unsigned int _seed)
  {
    generator->seed(_seed);
  }
  
};








// class that old mass action kinetics, in principle could be extended to handle other types of kinetics
class KineticLaw
{
public:
  KineticLaw(bool, float);
  ~KineticLaw();
  
  void fixedSeedMode(const string);
  
  void SteppingReactionRates(OwnedArray<SimReaction>&, float, int, bool);
  void SteppingInflowOutflowRates(OwnedArray<SimEntity>&, float, int);
  void SteppingDiffusionRates(OwnedArray<SimEntity>&, Patch&);
  
  bool useStochasticity;
  float noiseEpsilon;
  
  
private:
  
  RandomGausGenerator * rgg;

  
  
  
};




