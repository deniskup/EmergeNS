

#include "Simulation.h"
#include "Entity.h"
#include "Reaction.h"

using namespace std;

juce_ImplementSingleton(Simulation)

    Simulation::Simulation() : ControllableContainer("Simulation"),
                               Thread("Simulation")
{
}

Simulation::~Simulation()
{
  // Destructor
  stopThread(500);
}

void Simulation::setup(int m, Array<Entity *> e, Array<Reaction *> r)
{
  maxSteps->setValue(m);
  entities.clear();
  entities.addArray(e);
  reactions.clear();
  reactions.addArray(r);
}

void Simulation::start()
{
  startThread();
}

void Simulation::nextStep()
{
  if (curStep >= maxSteps)
  {
    stop();
    return;
  }
  // add primary->boolValue() entities
  for (auto &ent : entities)
  {
    if (ent->primary->boolValue())
    {
      ent->concent->setValue(ent->concent->floatValue()+ent->creationRate->floatValue());
    }
    ent->decrease(ent->concent->floatValue() * ent->destructionRate->floatValue());
  }

  // loop through reactions
  for (auto &reac : reactions)
  {

    Entity *e1 = dynamic_cast<Entity *>(reac->reactant1->targetContainer.get());
    if (e1 == nullptr)
      continue;
    Entity *e2 = dynamic_cast<Entity *>(reac->reactant2->targetContainer.get());
    if (e2 == nullptr)
      continue;
    Entity *p = dynamic_cast<Entity *>(reac->product->targetContainer.get());
    if (p == nullptr)
      continue;

    // compute product of reactants concentrations
    float reacConcent = e1->concent->floatValue() * e2->concent->floatValue();
    // compute product of products concentrations
    float prodConcent = p->concent->floatValue();

    // remove reactants

    e1->decrease(reacConcent * reac->assocRate->floatValue());
    e1->increase(prodConcent * reac->dissocRate->floatValue());
    e2->decrease(reacConcent * reac->assocRate->floatValue());
    e2->increase(prodConcent * reac->dissocRate->floatValue());

    // add products
    p->increase(reacConcent * reac->assocRate->floatValue());
    p->decrease(prodConcent * reac->dissocRate->floatValue());
  }

  curStep++;
  listeners.call(&SimulationListener::newStep, this);
}

void Simulation::stop()
{
  finished->setValue(true);
}

void Simulation::cancel()
{
  stopThread(500);
}

void Simulation::run()
{
  curStep->setValue(0);
  finished->setValue(false);
  while (!finished->boolValue() && !threadShouldExit())
  {
    nextStep();
    wait(20);
  }

  DBG("End thread");
  listeners.call(&SimulationListener::simulationFinished, this);
}
