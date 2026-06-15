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
//using namespace juce;
using namespace std;


class RandomGausGenerator
{
  public:
  RandomGausGenerator(float _mu, float _sigma) // constructor
    : generator(),
      gausDist(_mu, _sigma)
      //mu(_mu),
      //sigma(_sigma)
  {
    //gausDist = new normal_distribution<float>;
    //normal_distribution<float> dtemp(mu, sigma);
    //gausDist->param(dtemp.param());
    //generator=new default_random_engine;
  };

  
  // generate actual random number
  float randomNumber()
  {
    return (gausDist)(generator);
  }
  
  void setFixedSeed(unsigned int _seed)
  {
    generator.seed(_seed);
  }
  
  void shakeSeedValue()
  {
    generator.seed(rd());
  }

  private:

    random_device rd;
    default_random_engine generator;
    normal_distribution<float> gausDist;
    //float mu = 0.;
    //float sigma = 1.;
    //unsined long seed;
  
};








// class that old mass action kinetics, in principle could be extended to handle other types of kinetics
class KineticLaw
{
public:
  KineticLaw(bool, float);
  ~KineticLaw();
  
  void fixedSeedMode(const string);
  void shakeSeedValue();
  
  void SteppingReactionRates(juce::OwnedArray<SimReaction>&, float, int, bool);
  void SteppingInflowOutflowRates(juce::OwnedArray<SimEntity>&, float, int);
  void SteppingDiffusionRates(juce::OwnedArray<SimEntity>&, Patch&);
  
  bool useStochasticity;
  float noiseEpsilon;
  
  
private:
  
  RandomGausGenerator rgg;

};




