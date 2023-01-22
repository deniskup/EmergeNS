

#include "Simulation.h"
#include "EntityManager.h"
#include "ReactionManager.h"
#include "Generation.h"

using namespace std;

juce_ImplementSingleton(Simulation)

    Simulation::Simulation() : ControllableContainer("Simulation"),
                               Thread("Simulation"),
                               curStep(0),
                               simNotifier(1000) // max messages async that can be sent at once
{
  simNotifier.dropMessageOnOverflow = false;

  dt = addFloatParameter("dt", "time step in ms", .001, 0.f);
  totalTime = addFloatParameter("Total Time", "Total simulated time in seconds", 1.f, 0.f);
  perCent = addIntParameter("Progress", "Percentage of the simulation done", 0, 0, 100);
  perCent->setControllableFeedbackOnly(true);
  finished = addBoolParameter("Finished", "Finished", false);
  finished->setControllableFeedbackOnly(true);
  maxConcent = addFloatParameter("Max. Concent.", "Maximal concentration displayed on the graph", 5.f);
  realTime = addBoolParameter("Real Time", "Print intermediary steps of the simulation", false);
  generated = addBoolParameter("Generated", "Are the entities manually chosen or generated ?", false);
  startTrigger = addTrigger("Start", "Start");
  cancelTrigger = addTrigger("Cancel", "Cancel");
  autoScale = addBoolParameter("Auto Scale", "Automatically scale to maximal concentration reached", true);
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

int randInt(int i, int j)
{
  if (j < i)
  {
    LOGWARNING("Range [" << i << "," << j << "] incorrect, setting to " << i);
    return i;
  }
  if (i == j)
    return i;
  return Random::getSystemRandom().nextInt(Range(i, j + 1));
}

float randFloat()
{
  return Random::getSystemRandom().nextFloat();
}

float randFloat(float a, float b)
{
  if (b < a)
  {
    LOGWARNING("Range [" << a << "," << b << "] incorrect, setting to " << a);
    return a;
  }
  if (a == b)
    return a;
  float r = randFloat();
  return (r * a + (1 - r) * b);
}

void Simulation::fetchGenerate()
{
  Generation *gen = Generation::getInstance();

  int numLevels = randInt(gen->numLevels->x, gen->numLevels->y);

  // primary entities
  int primEnts = randInt(gen->primEntities->x, gen->primEntities->y);

  // only rough approximation
  int totalEnts = numLevels * gen->entPerLevNum->x;
  float propShow = (gen->avgNumShow->floatValue()) / totalEnts;
  int nbShow = 0;

  Array<Array<SimEntity *>> hierarchyEnt;
  Array<SimEntity *> primEnt;
  for (int idp = 0; idp < primEnts; idp++)
  {

    float concent = randFloat(gen->concentRange->x, gen->concentRange->y);
    float dRate = randFloat(0., gen->maxDestructionRate->floatValue());
    float cRate = randFloat(0., gen->maxCreationRate->floatValue());
    SimEntity *e = new SimEntity(true, concent, cRate, dRate, 0.f);
    e->level = 0;
    e->color = Colour::fromHSV(.3f * idp, 1, 1, 1);
    e->name = "prim" + String(idp);
    e->draw = false;
    if (nbShow < gen->avgNumShow->intValue() && randFloat() < propShow)
    { // proba to draw entity
      e->draw = true;
      nbShow++;
    }
    entities.add(e);
    primEnt.add(e);
  }
  hierarchyEnt.add(primEnt);

  // composite entities

  // poly or exp growth
  float aGrowth = gen->entPerLevA->floatValue();
  float bGrowth = gen->entPerLevB->floatValue();
  float u = gen->entPerLevUncert->intValue();

  // reactions per entity
  int minReacPerEnt = gen->reactionsPerEntity->x;
  int maxReacPerEnt = gen->reactionsPerEntity->y;
  for (int level = 1; level < numLevels; level++)
  {
    Array<SimEntity *> levelEnt;
    int numEnts = 1;
    switch (gen->growthEntitiesPerLevel->getValueDataAsEnum<Generation::GrowthMode>())
    {
    case Generation::CONSTANT:
      numEnts = randInt(gen->entPerLevNum->x, gen->entPerLevNum->y);
      break;
    case Generation::POLYNOMIAL:
      numEnts = (int)(aGrowth * pow(level, bGrowth) + randInt(-u, u));
      break;
    case Generation::EXPONENTIAL:
      numEnts = (int)(aGrowth * pow(primEnts, level) + randInt(-u, u));
      break;
    }
    if(numEnts<1) numEnts=1; //at least one entity per level, maybe not necessary later but needed for now.
    for (int ide = 0; ide < numEnts; ide++)
    {
      float concent = 0.; // no initial presence of composite entities
      float dRate = randFloat(0., gen->maxDestructionRate->floatValue()) / level;
      float uncert = gen->energyUncertainty->floatValue();
      float energy = -level * gen->energyPerLevel->floatValue() + randFloat(-uncert, uncert);
      SimEntity *e = new SimEntity(false, concent, 0., dRate, energy);
      e->level = level;
      e->color = Colour::fromHSV((randFloat()), 1, 1, 1); // random color
      e->name = String(level) + "-" + String(ide);
      e->draw = false;
      if (nbShow < gen->avgNumShow->intValue() && randFloat() < propShow)
      { // proba to draw entity
        e->draw = true;
        nbShow++;
      }
      entities.add(e);
      levelEnt.add(e);
      // reactions producing e
      int nbReac = randInt(minReacPerEnt, maxReacPerEnt);

      //compositions are not verified for now, just levels
      for (int ir = 0; ir < nbReac; ir++)
      {
        int lev1 = randInt(0, level - 1);
        int lev2 = level - lev1 - 1;
        int id1 = randInt(0, hierarchyEnt[lev1].size() - 1);
        int id2 = randInt(0, hierarchyEnt[lev2].size() - 1);
        SimEntity *e1 = hierarchyEnt[lev1][id1];
        SimEntity *e2 = hierarchyEnt[lev2][id2];

        float barrier = randFloat(0., gen->maxEnergyBarrier->floatValue());
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
        // NLOG(niceName, e1->name + " + " + e2->name + " -> " + e->name);
      }
    }
    hierarchyEnt.add(levelEnt);
  }
}

void Simulation::start()
{
  startTrigger->setEnabled(false);
  simNotifier.addMessage(new SimulationEvent(SimulationEvent::WILL_START, this));
  listeners.call(&SimulationListener::simulationWillStart, this);

  entities.clear();
  entitiesDrawn.clear();

  reactions.clear();
  if (generated->boolValue())
  {
    fetchGenerate();
  }
  else
  {
    fetchManual();
  }

  Array<float> entityValues;
  Array<Colour> entityColors;

  for (auto &ent : entities)
  {
    if (ent->draw)
    {
      entitiesDrawn.add(ent);
      entityValues.add(ent->concent);
      entityColors.add(ent->color);
    }
  }

  simNotifier.addMessage(new SimulationEvent(SimulationEvent::STARTED, this, 0, entityValues, entityColors));
  listeners.call(&SimulationListener::simulationStarted, this);
  recordConcent = 0.;
  recordDrawn = 0.;
  checkPoint = 20; // 20 checkpoints
  startThread();
}

void Simulation::nextStep()
{

  bool isCheck = (curStep % checkPoint == 0);
  if (displayLog && isCheck)
  {
    NLOG(niceName, "New Step : " << curStep);
    wait(1);
  }
  if (curStep >= maxSteps)
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

  curStep++;
  perCent->setValue((int)((curStep * 100) / maxSteps));

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

    if (ent->draw && ent->concent > recordDrawn)
    {
      recordDrawn = ent->concent;
      recordDrawnEntity = ent->name;
    }
  }

  if (displayLog)
  {
    for (auto &e : entities)
    {
      if (e->draw && displayLog)
        NLOG(niceName, e->toString());
    }
  }

  Array<float> entityValues;
  for (auto &ent : entitiesDrawn)
  {
    entityValues.add(ent->concent);
  }

  simNotifier.addMessage(new SimulationEvent(SimulationEvent::NEWSTEP, this, curStep, entityValues));
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
  curStep = 0;
  finished->setValue(false);
  while (!finished->boolValue() && !threadShouldExit())
  {
    nextStep();
  }

  NLOG(niceName, "End thread");
  NLOG(niceName, "Record Concentration: " << recordConcent << " for entity " << recordEntity);
  NLOG(niceName, "Record Drawn Concentration: " << recordDrawn << " for entity " << recordDrawnEntity);
  simNotifier.addMessage(new SimulationEvent(SimulationEvent::FINISHED, this));
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
    start();
  else if (t == cancelTrigger)
    cancel();
}

void Simulation::onContainerParameterChanged(Parameter *p)
{
  ControllableContainer::onContainerParameterChanged(p);
  if (p == dt || p == totalTime)
  {
    maxSteps = (int)(totalTime->floatValue() / dt->floatValue());
  }
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
