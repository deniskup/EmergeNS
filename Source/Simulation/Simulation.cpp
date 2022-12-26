

#include "Simulation.h"
#include "EntityManager.h"
#include "ReactionManager.h"

using namespace std;

juce_ImplementSingleton(Simulation)

    Simulation::Simulation() : ControllableContainer("Simulation"),
                               Thread("Simulation")
{
  maxSteps = addIntParameter("Max Steps", "Max Steps", 50, 0);
  curStep = addIntParameter("Cur Step", "Current step in the simulation", 0, 0, maxSteps->intValue());
  curStep->setControllableFeedbackOnly(true);
  finished = addBoolParameter("Finished", "Finished", false);
  finished->setControllableFeedbackOnly(true);

  startTrigger = addTrigger("Start", "Start");
  cancelTrigger = addTrigger("Cancel", "Cancel");
}

Simulation::~Simulation()
{
  // Destructor
  stopThread(500);
}

void Simulation::start()
{
  
  entities.clear();
  reactions.clear();

  for (auto &e : EntityManager::getInstance()->items)
  {
    if (!e->enabled->boolValue())
      continue;
    entities.add(new SimEntity(e));
  }
  
  for (auto &r : ReactionManager::getInstance()->items)
  {
    if (!r->shouldIncludeInSimulation())
      continue;
    reactions.add(new SimReaction(r));
  }
  listeners.call(&SimulationListener::simulationStarted, this);
  startThread();
}

void Simulation::nextStep()
{
  NLOG(niceName, "New Step : " << curStep->intValue());
  if (curStep->intValue() >= maxSteps->intValue())
  {
    stop();
    return;
  }
  // add primary->boolValue() entities
  for (auto &ent : entities)
  {
    if (ent->primary)
    {
      ent->concent += ent->creationRate;
    }
    ent->decrease(ent->concent * ent->destructionRate);
  }

  // loop through reactions
  for (auto &reac : reactions)
  {
    // compute product of reactants concentrations
    float reacConcent = reac->reactant1->concent * reac->reactant2->concent;
    // compute product of products concentrations
    float prodConcent = reac->product->concent;

    float directSpeed = reacConcent * reac->assocRate;
    float reverseSpeed = prodConcent * reac->dissocRate;

    // remove reactants
    reac->reactant1->decrease(directSpeed);
    reac->reactant1->increase(reverseSpeed);
    reac->reactant2->decrease(directSpeed);
    reac->reactant2->increase(reverseSpeed);

    // add products
    reac->product->increase(directSpeed);
    reac->product->decrease(reverseSpeed);
  }

  curStep->setValue(curStep->intValue() + 1);

  for (auto &e : entities)
    NLOG(niceName, " > Entity " << e->toString());

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

  NLOG(niceName, "End thread");
  listeners.call(&SimulationListener::simulationFinished, this);
}

SimEntity *Simulation::getSimEntityForEntity(Entity *e)
{
  for (auto &se : entities)
  {
    if (se->entity == e)
      return se;
  }
  return nullptr;
}

void Simulation::onContainerTriggerTriggered(Trigger *t)
{
  if (t == startTrigger)
    start();
  else if (t == cancelTrigger)
    cancel();
}

void Simulation::onContainerParameterChanged(Parameter *p)
{
  ControllableContainer::onContainerParameterChanged(p);
  if (p == maxSteps)
    curStep->setRange(0, maxSteps->intValue());
}

SimEntity::SimEntity(Entity *e) : SimEntity(e->primary->boolValue(), e->concent->floatValue(), e->creationRate->floatValue(), e->destructionRate->floatValue())
{
  name = e->niceName;
  entity = e;
  color = e->itemColor->getColor();
}

SimEntity::SimEntity(bool isPrimary, float concent, float cRate, float dRate) : primary(isPrimary), concent(concent), creationRate(cRate), destructionRate(dRate),
                                                                                name("New entity"), entity(nullptr)
{
}

void SimEntity::increase(float incr)
{
  concent += incr;
}

void SimEntity::decrease(float decr)
{
  concent = jmax(0.f, concent - decr);
}

String SimEntity::toString() const
{
  return "[Entity " + name + " : " + String(concent) + "]";
}

SimReaction::SimReaction(Reaction *r) : assocRate(r->assocRate->floatValue()),
                                        dissocRate(r->dissocRate->floatValue())
{
  reactant1 = Simulation::getInstance()->getSimEntityForEntity(dynamic_cast<Entity *>(r->reactant1->targetContainer.get()));
  reactant2 = Simulation::getInstance()->getSimEntityForEntity(dynamic_cast<Entity *>(r->reactant2->targetContainer.get()));
  product = Simulation::getInstance()->getSimEntityForEntity(dynamic_cast<Entity *>(r->product->targetContainer.get()));
}

SimReaction::SimReaction(SimEntity *r1, SimEntity *r2, SimEntity *p, float aRate, float dRate) : reactant1(r1), reactant2(r2), product(p), assocRate(aRate), dissocRate(dRate)
{
}
