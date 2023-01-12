

#include "Simulation.h"
#include "EntityManager.h"
#include "ReactionManager.h"
#include "Generation.h"

using namespace std;

juce_ImplementSingleton(Simulation)

    Simulation::Simulation() : ControllableContainer("Simulation"),
                               Thread("Simulation")
{
  dt = addFloatParameter("dt", "time step in ms", .001, 0);
  totalTime = addFloatParameter("Total Time", "Total simulated time in seconds", 1, 0);
  maxSteps = addIntParameter("Max Steps", "Max Steps", 1000, 0);
  curStep = addIntParameter("Progress", "Current step in the simulation", 0, 0, maxSteps->intValue());
  curStep->setControllableFeedbackOnly(true);
  perCent = addIntParameter("Progress", "Percentage of the simulation done", 0, 0, 100);
  perCent->setControllableFeedbackOnly(true);
  finished = addBoolParameter("Finished", "Finished", false);
  finished->setControllableFeedbackOnly(true);
  maxConcent = addFloatParameter("Max. Concent.", "Maximal concentration displayed on the graph", 5.f);
  realTime = addBoolParameter("Real Time", "Print intermediary steps of the simulation", false);
  generated = addBoolParameter("Generated", "Are the entities manually chosen or generated ?", false);
  startTrigger = addTrigger("Start", "Start");
  cancelTrigger = addTrigger("Cancel", "Cancel");
}

Simulation::~Simulation()
{
  // Destructor
  stopThread(500);
}

void Simulation::fetchManual()
{
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
}

void Simulation::fetchGenerate()
{
  Generation *gen = Generation::getInstance();

  int numLevels = gen->numLevels->intValue();
  int entitiesPerLevel = gen->entitiesPerLevel->intValue();
  int maxReacperEnt = gen->maxReactionsPerEntity->intValue();
  // primary entities
  int primEnts = entitiesPerLevel; // will be dissociated later

  int totalEnts = numLevels * entitiesPerLevel;
  float propShow = (gen->avgNumShow->floatValue()) / totalEnts;

  for (int idp = 0; idp < primEnts; idp++)
  {
    // to pick randomly later, just testing
    float concent = 1.;
    float cRate = .5;
    float dRate = .3;
    SimEntity *e = new SimEntity(true, concent, cRate, dRate, 0.f);
    e->level = 0;
    e->color = Colour::fromHSV(.3f * idp, 1, 1, 1);
    e->name = "prim" + String(idp);
    e->draw = (Random::getSystemRandom().nextFloat() < propShow); // proba to draw prim entity
    entities.add(e);
  }

  // composite entities
  for (int level = 1; level < numLevels; level++)
  {
    for (int ide = 0; ide < entitiesPerLevel; ide++)
    {
      float concent = 1.;
      float cRate = .5;
      float dRate = .3;
      float energy = -level / 10.;
      SimEntity *e = new SimEntity(true, concent, cRate, dRate, energy);
      e->level = level;
      e->color = Colour::fromHSV((Random::getSystemRandom().nextFloat()), 1, 1, 1); // random color
      e->name = String(level) + "-" + String(ide);
      e->draw = Random::getSystemRandom().nextFloat() < propShow; // proba to draw composite entity
      entities.add(e);

      // reaction producing e, no constraint for now just testing
      int id1 = Random::getSystemRandom().nextInt(entities.size() - 1);
      int id2 = Random::getSystemRandom().nextInt(entities.size() - 1);
      SimEntity *e1 = entities[id1];
      SimEntity *e2 = entities[id2];

      float barrier = Random::getSystemRandom().nextFloat();
      // GA+GB
      float energyLeft = e1->freeEnergy + e2->freeEnergy;
      // GAB
      float energyRight = e->freeEnergy;
      // total energy G* of the reaction: activation + max of GA+GB and GAB.
      float energyStar = barrier + jmax(energyLeft, energyRight);
      // k1=exp(GA+GB-G*)
      float aRate = exp(energyLeft - energyStar);
      // k2=exp(GAB-G*)
      float disRate = exp(energyRight - energyStar);
      reactions.add(new SimReaction(e1, e2, e, aRate, disRate));
    }
  }
}

void Simulation::start()
{
  startTrigger->setEnabled(false);
  listeners.call(&SimulationListener::simulationWillStart, this);
  entities.clear();
  reactions.clear();
  if (generated->boolValue())
  {
    fetchGenerate();
  }
  else
  {
    fetchManual();
  }

  listeners.call(&SimulationListener::simulationStarted, this);
  recordConcent = 0.;
  checkPoint = 20; // 20 checkpoints
  startThread();
}

void Simulation::nextStep()
{
  // TODO cap the concentration to absolute maximum, interrupt the simulation if reached.

  bool displayLog = (curStep->intValue() % checkPoint == 0);
  if (displayLog)
  {
    NLOG(niceName, "New Step : " << curStep->intValue());
    wait(1);
  }
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
      ent->concent += ent->creationRate * dt->floatValue();
    }
    ent->decrease(ent->concent * ent->destructionRate * dt->floatValue());
  }

  // loop through reactions
  for (auto &reac : reactions)
  {
    // shorter names
    float reac1Concent = reac->reactant1->concent;
    float reac2Concent = reac->reactant2->concent;
    float prodConcent = reac->product->concent;
    // compute product of reactants concentrations
    float reacConcent = reac1Concent * reac2Concent;

    float directIncr = reacConcent * reac->assocRate * dt->floatValue();
    float reverseIncr = prodConcent * reac->dissocRate * dt->floatValue();

    // adjust the increments depending on available entities
    directIncr = jmin(directIncr, reac1Concent, reac2Concent);
    reverseIncr = jmin(reverseIncr, prodConcent);

    // increase entities
    reac->reactant1->increase(reverseIncr);
    reac->reactant2->increase(reverseIncr);
    reac->product->increase(directIncr);

    // decrease entities
    reac->reactant1->decrease(directIncr);
    reac->reactant2->decrease(directIncr);
    reac->product->decrease(reverseIncr);
  }

  curStep->setValue(curStep->intValue() + 1);
  perCent->setValue((int)((curStep->intValue() * 100) / maxSteps->intValue()));

  for (auto &ent : entities)
  {
    if (isinf(ent->concent))
    {
      NLOG(niceName, "Concentration of entity " << ent->name << " exceeded capacity");
      finished->setValue(true);
      return;
    }
    if (ent->concent > recordConcent)
    {
      recordConcent = ent->concent;
      recordEntity = ent->name;
    }
  }

  if (displayLog)
  {
    for (auto &e : entities)
    {
      if (e->draw)
        NLOG(niceName, e->toString());
    }
  }
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
  }

  NLOG(niceName, "End thread");
  NLOG(niceName, "Record Concentration: " << recordConcent << " for entity " << recordEntity);
  listeners.call(&SimulationListener::simulationFinished, this);
  startTrigger->setEnabled(true);
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
    start(); // todo disable the trigger when simulation running
  else if (t == cancelTrigger)
    cancel();
}

void Simulation::onContainerParameterChanged(Parameter *p)
{
  ControllableContainer::onContainerParameterChanged(p);
  if (p == dt || p == totalTime)
  {
    maxSteps->setValue((int)(totalTime->floatValue() / dt->floatValue()));
  }
  if (p == maxSteps)
    curStep->setRange(0, maxSteps->intValue());
}

SimEntity::SimEntity(Entity *e) : SimEntity(e->primary->boolValue(), e->concent->floatValue(), e->creationRate->floatValue(), e->destructionRate->floatValue(), e->freeEnergy->floatValue())
{
  name = e->niceName;
  entity = e;
  color = e->itemColor->getColor();
}

SimEntity::SimEntity(bool isPrimary, float concent, float cRate, float dRate, float freeEnergy) : primary(isPrimary), concent(concent), creationRate(cRate), destructionRate(dRate), freeEnergy(freeEnergy),
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
