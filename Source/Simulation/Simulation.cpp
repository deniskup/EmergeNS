

#include "Simulation.h"

using namespace std;

// Entity::Entity(int x, bool b, float s, float c, float d)
// {
//   id = x;
//   basic = b;
//   concent = s;
//   creationRate = c;
//   destructionRate = d;
// }



juce_ImplementSingleton(Simulation)

Simulation::Simulation() :
  ControllableContainer("Simulation"),
  Thread("Simulation")
{
}

Simulation::~Simulation()
{
  //Destructor
  stopThread(500);
}

// void Simulation::setup(int m, Array<Entity *> e, Array<Reaction *> r)
// {
//   maxSteps = m;
//   entities.clear();
//   entities.addArray(e);
//   reactions.clear();
//   reactions.addArray(r);
//   nbReactions = reactions.size();
// }

// void Simulation::start()
// {
//   startThread();
// }

// void Simulation::nextStep()
// {
//   if (curStep >= maxSteps)
//   {
//     stop();
//     return;
//   }
//   // add basic entities
//   for (auto &ent : entities)
//   {
//     if (ent->basic)
//     {
//       ent->concent += ent->creationRate;
//     }
//     ent->decrease(ent->concent * ent->destructionRate);
//   }

//   // loop through reactions
//   for (auto &reac : reactions)
//   { 

//     // compute product of reactants concentrations
//     float reacConcent = 1;
//     for (auto consom : reac->reactants) reacConcent *= consom->concent;
//      // compute product of products concentrations
//     float prodConcent = 1;
//     for (auto prod : reac->products) prodConcent *= prod->concent;


//     // remove reactants
//     for (auto consom : reac->reactants) {
//       consom->decrease(reacConcent*reac->assocRate);
//       consom->increase(prodConcent*reac->dissocRate);
//     }
    
//      // add products
//     for (auto prod : reac->products){
//       prod->increase(reacConcent*reac->assocRate);
//       prod->decrease(prodConcent*reac->dissocRate);
//     } 
//   }

//   curStep++;
//   listeners.call(&SimulationListener::newStep, this);
// }

// void Simulation::stop()
// {
//   finished = true;
// }

// void Simulation::cancel()
// {
//   stopThread(500);
// }

void Simulation::run()
{
  // curStep = 0;
  // finished = false;
  // while (!finished && !threadShouldExit())
  // {
  //   nextStep();
  //   wait(20);
  // }

  // DBG("End thread");
  // listeners.call(&SimulationListener::simulationFinished, this);
}
