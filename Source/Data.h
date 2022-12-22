/*
  ==============================================================================

    Data.h
    Created: 19 Dec 2022 6:31:28pm
    Author:  denis

  ==============================================================================
*/

#pragma once

#include <JuceHeader.h>
using namespace juce;
using namespace std;

class Entity
{
public:
  Entity(int x, bool b, float s, float c, float d);
  ~Entity() {}

  int id;
  bool basic;
  float concent;
  float creationRate; // absolute
  float destructionRate; // proportional to concentration

  void increase(float incr);
  void decrease(float decr);
};

class Reaction
{
public:
  Array<Entity *> reactants;
  Array<Entity *> products;
  float assocRate; // from reactants to product
  float dissocRate; //vice versa
  Reaction(Array<Entity *> r, Array<Entity *> p, float ar, float dr)
  {
    reactants = r;
    products = p;
    assocRate = ar;
    dissocRate = dr;
  }
  ~Reaction() {}
};

class Simulation : 
public ChangeBroadcaster,
public Thread
{
public:
  juce_DeclareSingleton(Simulation, true);
  Simulation();
  ~Simulation();

  int maxSteps = 0;
  int curStep = 0;
  bool finished = false;
  OwnedArray<Entity> entities;    // all entities
  OwnedArray<Reaction> reactions; // all reactions
  int nbReactions;

  void setup(int m, Array<Entity *> e, Array<Reaction *> r);
  void start();
  void nextStep();
  void stop();
  void cancel();
  
  void run() override;
};
