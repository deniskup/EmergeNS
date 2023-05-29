#include "Simulation.h"
#include "EntityManager.h"
#include "ReactionManager.h"
#include "Generation.h"
#include "Settings.h"

using namespace std;

juce_ImplementSingleton(Simulation)

    Simulation::Simulation() : ControllableContainer("Simulation"),
                               Thread("Simulation"),
                               curStep(0),
                               ready(false),
                               simNotifier(1000), // max messages async that can be sent at once
                               pacList(new PAClist(this))
{
  simNotifier.dropMessageOnOverflow = false;

  dt = addFloatParameter("dt", "time step in ms", .001, 0.f);
  totalTime = addFloatParameter("Total Time", "Total simulated time in seconds", 1.f, 0.f);
  pointsDrawn = addIntParameter("Checkpoints", "Number of checkpoints to draw points and observe RACs", 100, 1);
  perCent = addIntParameter("Progress", "Percentage of the simulation done", 0, 0, 100);
  perCent->setControllableFeedbackOnly(true);
  finished = addBoolParameter("Finished", "Finished", false);
  finished->setControllableFeedbackOnly(true);
  maxConcent = addFloatParameter("Max. Concent.", "Maximal concentration displayed on the graph", 5.f);
  realTime = addBoolParameter("Real Time", "Print intermediary steps of the simulation", false);
  // loadToManualByDefault = addBoolParameter("AutoLoad to Lists", "Automatically load the current simulation to manual lists", true);
  genTrigger = addTrigger("Generate", "Generate");
  startTrigger = addTrigger("Continue", "Continue");
  genstartTrigger = addTrigger("Gen. & Start", "Gen. & Start");
  restartTrigger = addTrigger("Start", "Start");
  cancelTrigger = addTrigger("Cancel", "Cancel");
  autoScale = addBoolParameter("Auto Scale", "Automatically scale to maximal concentration reached", true);
  oneColor = addBoolParameter("Unicolor", "Use only one color for each RAC", true);
  detectEquilibrium = addBoolParameter("Detect Equil.", "Detect equilibrium and stop simulation", false);
  epsilonEq = addFloatParameter("Eps.", "Epsilon for equilibrium detection", 0.001f, 0.f, 1.f);
  // ready = addBoolParameter("Ready","Can the simulation be launched ?", false);

  ignoreFreeEnergy = addBoolParameter("Ignore Free Energy", "Ignore free energy of entities in the simulation", false);
  ignoreBarriers = addBoolParameter("Ignore Barriers", "Ignore barrier energy of reactions in the simulation", false);
}

Simulation::~Simulation()
{
  // Destructor
  stopThread(500);
}

// maybe rand functions to move to a file Util.c later
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

float randFloat(float a)
{
  return randFloat(0.f, a);
}

void Simulation::clearParams()
{
  entities.clear();
  entitiesDrawn.clear();
  primEnts.clear();
  reactions.clear();
  pacList->clear();
  ready = false;
  numLevels = -1;
}

void Simulation::updateParams()
{
  // set entities drawn and primary
  entitiesDrawn.clear();
  primEnts.clear();

  for (auto &ent : entities)
  {
    if (ent->draw)
      entitiesDrawn.add(ent);
    if (ent->primary)
      primEnts.add(ent);
    numLevels = jmax(numLevels, ent->level);
  }

  // update the parameters of the simulation in the UI
  simNotifier.addMessage(new SimulationEvent(SimulationEvent::UPDATEPARAMS, this));
}

// to save additional data, different from getJSONdata()
var Simulation::toJSONData()
{
  var data = new DynamicObject();
  data.getDynamicObject()->setProperty("ready", ready);
  data.getDynamicObject()->setProperty("recordConcent", recordConcent);
  data.getDynamicObject()->setProperty("recordEntity", recordEntity);
  data.getDynamicObject()->setProperty("recordDrawn", recordDrawn);
  data.getDynamicObject()->setProperty("recordDrawnEntity", recordDrawnEntity);
  data.getDynamicObject()->setProperty("numLevels", numLevels);
  data.getDynamicObject()->setProperty("PACsGenerated", PACsGenerated);

  // entities
  var ents;
  for (auto &e : entities)
  {
    var ent = e->toJSONData();
    ents.append(ent);
  }
  data.getDynamicObject()->setProperty("entities", ents);

  // reactions
  var reacs;
  for (auto &r : reactions)
  {
    var reac = r->toJSONData();
    reacs.append(reac);
  }
  data.getDynamicObject()->setProperty("reactions", reacs);

  // primary entities
  var prim_ents;
  for (auto &e : primEnts)
  {
    var coord = new DynamicObject();
    coord.getDynamicObject()->setProperty("ent_id", e->id);
    prim_ents.append(coord);
  }
  data.getDynamicObject()->setProperty("primEnts", prim_ents);

  // entitiesDrawn
  // var entDrawn;
  // for (auto &e : entitiesDrawn)
  // {
  //   var coord = new DynamicObject();
  //   coord.getDynamicObject()->setProperty("ent_id", e->id);
  //   entDrawn.append(coord);
  // }
  // data.getDynamicObject()->setProperty("entitiesDrawn", entDrawn);

  // cycles
  // todo: JSON for paclist
  var cycs;
  for (auto &c : pacList->cycles)
  {
    var cyc = c->toJSONData();
    cycs.append(cyc);
  }
  data.getDynamicObject()->setProperty("cycles", cycs);

  return data;
}

void Simulation::importJSONData(var data)
{
  clearParams();
  if (data.isVoid())
    return;
  if (data.getDynamicObject() == nullptr)
    return;

  if (data.getDynamicObject()->hasProperty("ready"))
    ready = data.getDynamicObject()->getProperty("ready");
  if (data.getDynamicObject()->hasProperty("recordConcent"))
    recordConcent = data.getDynamicObject()->getProperty("recordConcent");
  if (data.getDynamicObject()->hasProperty("recordEntity"))
    recordEntity = data.getDynamicObject()->getProperty("recordEntity");
  if (data.getDynamicObject()->hasProperty("recordDrawn"))
    recordDrawn = data.getDynamicObject()->getProperty("recordDrawn");
  if (data.getDynamicObject()->hasProperty("numLevels"))
    numLevels = data.getDynamicObject()->getProperty("numLevels");
  // To move to PACList later
  if (data.getDynamicObject()->hasProperty("PACsGenerated"))
    PACsGenerated = data.getDynamicObject()->getProperty("PACsGenerated");

  // entities
  entities.clear();
  if (data.getDynamicObject()->hasProperty("entities"))
  {
    if (!data.getDynamicObject()->getProperty("entities").isArray())
    {
      LOGWARNING("Incomplete .ens file, entities of active sim cannot be loaded");
      return;
    }
    auto ents = data.getDynamicObject()->getProperty("entities").getArray();
    for (auto &evar : *ents)
    {
      entities.add(new SimEntity(evar));
    }
  }

  // reactions
  reactions.clear();
  if (data.getDynamicObject()->hasProperty("reactions"))
  {
    if (!data.getDynamicObject()->getProperty("reactions").isArray())
    {
      LOGWARNING("Incomplete .ens file, reactions of active sim cannot be loaded");
      return;
    }
    auto reacs = data.getDynamicObject()->getProperty("reactions").getArray();
    for (auto &rvar : *reacs)
    {
      reactions.add(new SimReaction(rvar));
    }
  }

  // entitiesDrawn
  // entitiesDrawn.clear();
  // if (data.getDynamicObject()->hasProperty("entitiesDrawn"))
  // {
  //   // todo verify array
  //   auto entDrawns = data.getDynamicObject()->getProperty("entitiesDrawn").getArray();
  //   for (auto &coord : *entDrawns)
  //   {
  //     entitiesDrawn.add(getSimEntityForID(coord["ent_id"]));
  //   }
  // }
  // primEnts
  primEnts.clear();
  if (data.getDynamicObject()->hasProperty("primEnts"))
  {
    auto prim_ents = data.getDynamicObject()->getProperty("primEnts").getArray();
    for (auto &coord : *prim_ents)
    {
      primEnts.add(getSimEntityForID(coord["ent_id"]));
    }
  }

  // cycles
  // a remplacer avec pacList->importJSONData
  pacList->cycles.clear();
  if (PACsGenerated && data.getDynamicObject()->hasProperty("cycles"))
  {
    auto cycs = data.getDynamicObject()->getProperty("cycles").getArray();
    if (cycs != nullptr)
    {
      for (auto &cvar : *cycs)
      {
        pacList->addCycle(new PAC(cvar, this));
      }
    }
  }
  ready = true;
  computeBarriers();
  updateParams();
  toImport = false;
}

void Simulation::importFromManual()
{
  LOG("Importing from manual lists");
  for (auto &e : entities)
  {
    if (e->toImport)
    {
      e->importFromManual();
      e->toImport = false;
    }
  }
  for (auto &r : reactions)
  {
    if (r->toImport)
    {
      r->importFromManual();
      r->toImport = false;
    }
  }

  updateParams();
}

void Simulation::computeRates()
{
  for (auto &r : reactions)
  {
    r->computeRate(ignoreBarriers->boolValue(), ignoreFreeEnergy->boolValue());
  }
}

void Simulation::computeBarriers()
{
  for (auto &r : reactions)
  {
    r->computeBarrier();
  }
}

void Simulation::fetchManual()
{
  clearParams();
  for (auto &e : EntityManager::getInstance()->items)
  {
    if (!e->enabled->boolValue())
      continue;
    auto se = new SimEntity(e);
    entities.add(se);
  }

  for (auto &r : ReactionManager::getInstance()->items)
  {
    if (!r->shouldIncludeInSimulation())
      continue;
    reactions.add(new SimReaction(r));
  }

  // todo compute levels and primary entities

  ready = true;
  updateParams();
}

void Simulation::loadToManualMode()
{
  // clear previous  (beware of the order !)
  ReactionManager *rm = ReactionManager::getInstance();
  rm->clear();

  EntityManager *em = EntityManager::getInstance();
  em->clear();

  // load entities
  for (auto &se : entities)
  {
    Entity *e = new Entity(se);
    // e->fromSimEntity(se);
    em->addItem(e, var(), false); // addtoUndo to false
  }

  // load reactions
  for (auto &sr : reactions)
  {
    Reaction *r = new Reaction(sr);
    //    r->fromSimReaction(sr);
    rm->addItem(r, var(), false);
  }
}

void Simulation::fetchGenerate()
{
  clearParams();
  Generation *gen = Generation::getInstance();

  numLevels = gen->numLevels->intValue(); // randInt(gen->numLevels->x, gen->numLevels->y);

  // primary entities
  int nbPrimEnts = gen->primEntities->intValue(); // randInt(gen->primEntities->x, gen->primEntities->y);

  // only rough approximation, useful only for drawing
  int totalEnts = numLevels * gen->entPerLevNum->intValue();
  const float propShow = (gen->avgNumShow->floatValue()) / totalEnts;
  int nbShow = 0;

  int cur_id = 0;

  Array<Array<SimEntity *>> hierarchyEnt;

  // Array<SimEntity *> primEnts; primEnts is part of Simulation

  const float initConcentBase = gen->initConcent->x;
  const float initConcentVar = gen->initConcent->y;
  const float dRateBase = gen->destructionRate->x;
  const float dRateVar = gen->destructionRate->y;
  const float cRateBase = gen->creationRate->x;
  const float cRateVar = gen->creationRate->y;

  const float energyCoef = gen->energyPerLevel->x;
  const float energyVar = gen->energyPerLevel->y;

  const float energyBarrierBase = gen->energyBarrier->x;
  const float energyBarrierVar = gen->energyBarrier->y;

  // recall that energy of primary entities are normalized to 0

  for (int idp = 0; idp < nbPrimEnts; idp++)
  {

    const float concent = jmax(0.f, initConcentBase + randFloat(-initConcentVar, initConcentVar));
    const float dRate = jmax(0.f, dRateBase + randFloat(-dRateVar, dRateVar));
    const float cRate = jmax(0.f, cRateBase + randFloat(-cRateVar, cRateVar));
    SimEntity *e = new SimEntity(true, concent, cRate, dRate, 0.f);
    e->level = 1;
    e->id = cur_id;
    e->freeEnergy = 0;
    cur_id++;
    e->color = Colour::fromHSV(randFloat(.2), 1, 1, 1);
    e->draw = false;
    if (gen->showAll->boolValue())
    {
      e->draw = true;
      nbShow++;
    }
    else
    {
      if (nbShow < gen->avgNumShow->intValue() && randFloat() < propShow)
      { // proba to draw entity
        e->draw = true;
        nbShow++;
      }
    }
    e->composition.insertMultiple(0, 0, nbPrimEnts);
    e->composition.set(idp, 1);
    e->nameFromCompo();
    entities.add(e);
    primEnts.add(e);
  }
  // add dummy level 0
  hierarchyEnt.add(Array<SimEntity *>());

  // primEnts at level 1
  hierarchyEnt.add(primEnts);

  // composite entities

  // poly growth
  const float aGrowth = gen->entPerLevA->floatValue();
  const float bGrowth = gen->entPerLevB->floatValue();
  const int u = gen->entPerLevUncert->intValue();

  // proportional of total
  // const float propEnt = gen->propEntities->floatValue();

  const float propReac = gen->propReactions->floatValue();

  // reactions per entity, to change
  const int minReacPerEnt = gen->reactionsPerEntity->intValue();
  const int maxReacPerEnt = gen->reactionsPerEntity->intValue(); // parameter to add

  // multisets[i][j] is the number of multisets of size i with j elements, i.e. the number of entities of size i with j primary entiies
  vector<vector<int>> multisets(numLevels + 1, vector<int>(nbPrimEnts + 1, 0));

  // just for lisibility
  enum genMode
  {
    CONSTANT,
    POLYNOMIAL,
    PROPREACTIONS
  };

  genMode mode;

  switch (gen->growthEntitiesPerLevel->getValueDataAsEnum<Generation::GrowthMode>())
  {
  case Generation::CONSTANT:
    mode = CONSTANT;
    break;
  case Generation::POLYNOMIAL:
    mode = POLYNOMIAL;
    break;
  case Generation::PROPREACTIONS:
    mode = PROPREACTIONS;
    break;
  }

  for (int i = 0; i <= numLevels; ++i)
  {
    for (int j = 0; j <= nbPrimEnts; ++j)
    {
      if (i == 0)
      {
        multisets[i][j] = 1;
        continue;
      }
      if (j == 0)
      {
        multisets[i][j] = 0;
        continue;
      }

      multisets[i][j] = multisets[i][j - 1] + multisets[i - 1][j];
    }
  }

  for (int level = 2; level <= numLevels; level++)
  {
    Array<SimEntity *> levelEnt;
    int numEnts = 1;
    switch (mode)
    {
    case CONSTANT:
      numEnts = gen->entPerLevNum->intValue();
      break;
    case POLYNOMIAL:
      numEnts = (int)(aGrowth * pow(level, bGrowth) + randInt(-u, u));
      break;
      // case PROPORTION:
      //   //
      //   const int entsMaxAtLevel = multisets[level + 1][nbPrimEnts];
      //   numEnts = (int)(propEnt * entsMaxAtLevel);
      //   break;
      // no need to fix numEnts for PROPREACTIONS
    }
    numEnts = jmax(1, numEnts); // at least one entity per level, maybe not necessary later but needed for now.

    // list all possible compositions from previous entities
    // recall that CompoDecomps is a struct with a composition and a list of decompositions
    Array<CompoDecomps *> compos; // first working thing, Hashtable or sorted array later ?
    for (int lev1 = 1; lev1 < level; lev1++)
    {
      int lev2 = level - lev1; // complement level
      if (lev2 < lev1)
        break; // no need to do the reverse cases
      // compute all combinations
      for (auto &ent1 : hierarchyEnt[lev1])
      {
        for (auto &ent2 : hierarchyEnt[lev2])
        {
          Array<int> newCompo;
          for (int i = 0; i < nbPrimEnts; i++)
          {
            newCompo.add(ent1->composition[i] + ent2->composition[i]);
          }
          // loop through existing ones
          bool exists = false;
          for (auto &cd : compos)
          {
            if (cd->compo == newCompo)
            { // if exists
              // NLOG("Compos","Exists "<<ent1->name<< " + "<<ent2->name);
              cd->add(ent1, ent2);
              exists = true;
              break;
            }
          }
          if (!exists)
          {
            //  NLOG("Compos","New "<<ent1->name<< " + "<<ent2->name);
            Array<Decomp> dec(make_pair(ent1, ent2));
            compos.add(new CompoDecomps(newCompo, dec));
          }
          if (lev1 == lev2 && ent1 == ent2)
            break; // to avoid duplicates, we stop when reaching the diagonal
        }
      }
    }
    // bound numEnts by the number of compositions.
    // NLOG("Compos", compos.size() << " at level " << level);

    numEnts = jmin(numEnts, compos.size());
    bool finishedEntities = false;
    int ide = 0;
    while (!finishedEntities)
    {
      const float concent = 0.; // no initial presence of composite entities
      // float dRate = randFloat(0., gen->maxDestructionRate->floatValue()) / level;
      const float dRate = jmax(0.f, dRateBase + randFloat(-dRateVar, dRateVar));

      const float energy = level * energyCoef + randFloat(-energyVar, energyVar);
      SimEntity *e = new SimEntity(false, concent, 0., dRate, energy);
      e->level = level;
      e->color = Colour::fromHSV(level * 1. / numLevels + randFloat(.2), 1, 1, 1); // color depends only on level
      e->draw = false;
      e->id = cur_id;
      cur_id++;
      if (gen->showAll->boolValue())
      {
        e->draw = true;
        nbShow++;
      }
      else
      {
        if (nbShow < gen->avgNumShow->intValue() && randFloat() < propShow)
        { // proba to draw entity
          e->draw = true;
          nbShow++;
        }
      }
      int idComp = randInt(0, compos.size() - 1);
      e->composition = compos[idComp]->compo;
      // NLOG("New entity", e->name << " = " << dec.first->name << " + " << dec.second->name);
      e->nameFromCompo();
      entities.add(e);
      levelEnt.add(e);

      // reactions producing e
      int nbReac = randInt(minReacPerEnt, maxReacPerEnt);
      int nbDecomps = compos[idComp]->decomps.size();
      nbReac = jmin(nbReac, nbDecomps);

      // we are looping throug possible rections to create the entity e
      int nbReacDone = 0;
      bool reacFinished = false;
      while (!reacFinished)
      {
        int idDecomp = randInt(0, compos[idComp]->decomps.size() - 1);
        if (mode != PROPREACTIONS || randFloat() < propReac)
        {
          SimEntity *e1 = compos[idComp]->decomps[idDecomp].first;
          SimEntity *e2 = compos[idComp]->decomps[idDecomp].second;

          // choice of activation barrier
          float barrier = energyBarrierBase + randFloat(-energyBarrierVar, energyBarrierVar);
          auto reac = new SimReaction(e1, e2, e, 0., 0., barrier);
          reac->computeRate(false, false);
          reac->setName();
          // NLOG("New reaction",reac->name << " with assoc rate " << reac->assocRate << " and dissoc rate " << reac->dissocRate);
          reactions.add(reac);

          // NLOG("New reaction", e->name << " = " << e1->name << " + " << e2->name);
          nbReacDone++;
        }
        // remove this decomposition
        compos[idComp]->decomps.remove(idDecomp);
        if (nbReacDone == nbReac && mode != PROPREACTIONS)
          reacFinished = true;
        if (compos[idComp]->decomps.size() == 0)
          reacFinished = true;
      }
      compos.remove(idComp);
      ide++;
      if (ide == numEnts && mode != PROPREACTIONS)
        finishedEntities = true;
      if (compos.size() == 0)
        finishedEntities = true;
    }

    hierarchyEnt.add(levelEnt);
  }
  // ready->setValue(true);
  ready = true;

  LOG("Generated " << entities.size() << " entities and " << reactions.size() << " reactions");
  updateParams();

  if (Settings::getInstance()->autoLoadLists->boolValue() && !express)
    loadToManualMode();
}

void Simulation::start(bool restart)
{
  if (!ready)
  {
    LOGWARNING("No simulation loaded, using manual lists");
    fetchManual();
  }
  else
  {
    if (!express) importFromManual(); // import entities and reactions from manual lists, only those who have been changed
  }

  if (restart)
  {
    for (auto &e : entities)
    {
      e->concent = e->startConcent;
    }
  }

  //computeRates(); // compute reactions rates to take into account the ignored energies

  startTrigger->setEnabled(false);
  if(!express) simNotifier.addMessage(new SimulationEvent(SimulationEvent::WILL_START, this));
  // listeners.call(&SimulationListener::simulationWillStart, this);

  Array<float> entityValues;
  Array<Colour> entityColors;

  for (auto &ent : entitiesDrawn)
  {
    entityValues.add(ent->concent);
    entityColors.add(ent->color);
  }

  if(!express) simNotifier.addMessage(new SimulationEvent(SimulationEvent::STARTED, this, 0, entityValues, entityColors));
  // listeners.call(&SimulationListener::simulationStarted, this);
  recordConcent = 0.;
  recordDrawn = 0.;

  // remove RACs
  for (auto &pac : pacList->cycles)
  {
    pac->wasRAC = false;
  }

  checkPoint = maxSteps / pointsDrawn->intValue(); // draw once every "chekpoints" steps
  checkPoint = jmax(1, checkPoint);
  startThread();
}

void Simulation::nextStep()
{

  bool isCheck = (curStep % checkPoint == 0);
  if (displayLog && isCheck)
  {
    LOG("New Step : " << curStep);
    wait(1);
  }
  if (curStep >= maxSteps && !express) // in express mode we wait for the equilibrium
  {
    stop();
    return;
  }
  // add primary->boolValue() entities
  for (auto &ent : entities)
  {
    ent->previousConcent = ent->concent; // save concent in previousConcent to compute var speed
    if (ent->primary)
    {
      ent->concent += ent->creationRate * dt->floatValue();
    }
    ent->decrease(ent->concent * ent->destructionRate * dt->floatValue());
  }

  // loop through reactions
  for (auto &reac : reactions)
  {
    if (!reac->enabled)
      continue;
    // shorter names
    float reac1Concent = reac->reactant1->concent;
    float reac2Concent = reac->reactant2->concent;
    float prodConcent = reac->product->concent;
    // compute product of reactants concentrations
    float reacConcent = reac1Concent * reac2Concent;

    float directCoef = reacConcent * reac->assocRate;
    float reverseCoef = prodConcent * reac->dissocRate;

    float directIncr = directCoef * dt->floatValue();
    float reverseIncr = reverseCoef * dt->floatValue();

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

    // update flow needed only at checkpoints
    if (isCheck)
    {
      if (directCoef - reverseCoef > 0)
      {
        reac->flow = directCoef - reverseCoef;
        reac->flowdir = false;
      }
      else
      {
        reac->flow = reverseCoef - directCoef;
        reac->flowdir = true;
      }
    }
  }

  curStep++;
  perCent->setValue((int)((curStep * 100) / maxSteps));

  float maxVar = 0.;

  for (auto &ent : entities)
  {
    if (isinf(ent->concent))
    {
      LOG("Concentration of entity " << ent->name << " exceeded capacity");
      finished->setValue(true);
      return;
    }
    if (ent->concent > recordConcent)
    {
      recordConcent = ent->concent;
      recordEntity = ent->name;
    }

    float variation = abs(ent->concent - ent->previousConcent);
    maxVar = jmax(maxVar, variation);

    if (ent->draw && ent->concent > recordDrawn)
    {
      recordDrawn = ent->concent;
      recordDrawnEntity = ent->name;
    }
  }
  maxVarSpeed = maxVar / dt->floatValue();

  if (displayLog)
  {
    for (auto &e : entities)
    {
      if (e->draw && displayLog)
        LOG(e->toString());
    }
  }
  bool stopAtEquilibrium = detectEquilibrium->boolValue() || express;
  if (stopAtEquilibrium && maxVarSpeed < epsilonEq->floatValue())
  {
    if (!express)
      LOG("Equilibrium reached after time " << curStep * dt->floatValue() << " s with max speed " << maxVarSpeed);
    stop();
  }
  // rest only to call only pointsDrawn time
  if (!isCheck)
    return;

  // for now we don't care about RACs in express mode
  if (express)
    return;

  // storing current concentrations for drawing
  Array<float> entityValues;
  for (auto &ent : entitiesDrawn)
  {
    entityValues.add(ent->concent);
  }

  // compute RACs
  Array<float> PACsValues;
  Array<bool> RACList;
  // cout << setprecision(3);
  int idPAC = 0;
  for (auto &cycle : pacList->cycles)
  {
    idPAC++;
    bool newRAC = (cycle->flow == 0.);
    SimReaction *minreac = cycle->reacDirs[0].first;
    cycle->flow = minreac->flow; // initialisation to a max potential value
    ;
    for (auto &reacDir : cycle->reacDirs)
    {
      auto reac = reacDir.first;
      bool dir = reacDir.second;

      if (dir != (reac->flowdir) || !(reac->enabled))
      { // wrong direction
        cycle->flow = 0.;
        continue;
      }
      if (reac->flow < cycle->flow)
      {
        cycle->flow = reac->flow;
        minreac = reac;
      }
    }
    PACsValues.add(cycle->flow);
    if (cycle->flow > 0)
    {
      cout << "RAC Flow " << cycle->flow << "  " << cycle->toString() << endl;
      cycle->wasRAC = true;
      if (newRAC)
        LOG("RAC " << idPAC << " from min reac " << minreac->name);
      if (cycle->flow > pacList->maxRAC)
        pacList->maxRAC = cycle->flow;
    }
    RACList.add(cycle->wasRAC);
  }
  cout << "-" << endl;

  simNotifier.addMessage(new SimulationEvent(SimulationEvent::NEWSTEP, this, curStep, entityValues, {}, PACsValues, RACList));
  // listeners.call(&SimulationListener::newStep, this);
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
  LOG("--------- Start thread ---------");
  finished->setValue(false);
  while (!finished->boolValue() && !threadShouldExit())
  {
    nextStep();
  }

  LOG("--------- End thread ---------");

  if (express)
  {
    writeJSONConcents();
    return;
  }
  
  LOG("Record Concentration: " << recordConcent << " for entity " << recordEntity);
  if (recordDrawn < recordConcent)
    LOG("Record Drawn Concentration: " << recordDrawn << " for entity " << recordDrawnEntity);
  LOG("Max RAC: " << pacList->maxRAC);
  LOG("RACS:");

  pacList->printRACs();


  updateConcentLists();
  simNotifier.addMessage(new SimulationEvent(SimulationEvent::FINISHED, this));
  // listeners.call(&SimulationListener::simulationFinished, this);
  startTrigger->setEnabled(true);
}

void Simulation::writeJSONConcents(string filename)
{
  if (filename == "")
    filename = "concentrations.json";
  ofstream concentFile;
  concentFile.open(filename, ofstream::out | ofstream::trunc);
  concentFile << JSON::toString(concent2JSON());
  LOG("Concentrations written to " << filename);
}

var Simulation::concent2JSON()
{
  var data = new DynamicObject();
  for (auto &e : entities)
  {
    var ent = new DynamicObject();
    ent.getDynamicObject()->setProperty("Start", e->startConcent);
    ent.getDynamicObject()->setProperty("End", e->concent);
    data.getDynamicObject()->setProperty(e->name, ent);
  }
  return data;
}

SimEntity *Simulation::getSimEntityForID(int id)
{
  for (auto &se : entities)
  {
    if (se->id == id)
      return se;
  }
  jassertfalse;
  return nullptr;
}

SimReaction *Simulation::getSimReactionForID(int idSAT)
{
  for (auto &sr : reactions)
  {
    if (sr->idSAT == idSAT)
      return sr;
  }
  jassertfalse;
  return nullptr;
}

void Simulation::updateConcentLists()
{
  if(express) return;
  for (auto &ent : EntityManager::getInstance()->items)
  {
    auto se = ent->simEnt;
    if (se != nullptr)
    {
      ent->concent->setValue(se->concent);
    }
    else
    {
      LOGWARNING("No SimEntity for entity " << ent->niceName);
    }
  }
}

void Simulation::onContainerTriggerTriggered(Trigger *t)
{
  express= detectEquilibrium->boolValue();
  if (t == genTrigger)
  {
    fetchGenerate();
  }
  else if (t == genstartTrigger)
  {
    fetchGenerate();
    start(true);
  }
  else if (t == restartTrigger)
  {
    start(true);
  }
  else if (t == startTrigger)
  {
    start(false);
  }

  else if (t == cancelTrigger)
    cancel();
}

void Simulation::onContainerParameterChanged(Parameter *p)
{
  ControllableContainer::onContainerParameterChanged(p);
  if (p == dt || p == totalTime)
  {
    maxSteps = (int)(totalTime->floatValue() / dt->floatValue());
    maxSteps = jmax(1, maxSteps);
  }
  if (p == detectEquilibrium)
  {
    epsilonEq->hideInEditor = !detectEquilibrium->boolValue();
  }
}

SimEntity::SimEntity(Entity *e) : SimEntity(e->primary->boolValue(), e->startConcent->floatValue(), e->creationRate->floatValue(), e->destructionRate->floatValue(), e->freeEnergy->floatValue())
{
  name = e->niceName;
  entity = e;
  color = e->itemColor->getColor();
  draw = e->draw->boolValue();
  level = e->level;
  e->simEnt = this;
}

SimEntity::SimEntity(bool isPrimary, float concent, float cRate, float dRate, float freeEnergy) : primary(isPrimary), concent(concent), startConcent(concent), creationRate(cRate), destructionRate(dRate), freeEnergy(freeEnergy),
                                                                                                  name("New entity"), entity(nullptr)
{
}

var color2JSON(Colour col)
{
  var data = new DynamicObject();
  data.getDynamicObject()->setProperty("H", col.getHue());
  data.getDynamicObject()->setProperty("S", col.getSaturation());
  data.getDynamicObject()->setProperty("B", col.getBrightness());
  data.getDynamicObject()->setProperty("A", col.getAlpha());
  return data;
}

Colour JSON2Color(var data)
{
  return Colour::fromHSV(data["H"], data["S"], data["B"], data["A"]);
}

SimEntity::SimEntity(var data)
{
  if (data.isVoid())
    return;
  if (data.getDynamicObject() == nullptr)
    return;

  if (data.getDynamicObject()->hasProperty("name"))
    name = data.getDynamicObject()->getProperty("name");

  if (data.getDynamicObject()->hasProperty("color"))
    color = JSON2Color(data.getDynamicObject()->getProperty("color"));

  if (data.getDynamicObject()->hasProperty("primary"))
    primary = data.getDynamicObject()->getProperty("primary");

  if (data.getDynamicObject()->hasProperty("id"))
    id = data.getDynamicObject()->getProperty("id");

  if (data.getDynamicObject()->hasProperty("concent"))
    concent = data.getDynamicObject()->getProperty("concent");

  if (data.getDynamicObject()->hasProperty("startConcent"))
    startConcent = data.getDynamicObject()->getProperty("startConcent");

  if (data.getDynamicObject()->hasProperty("creationRate"))
    creationRate = data.getDynamicObject()->getProperty("creationRate");

  if (data.getDynamicObject()->hasProperty("destructionRate"))
    destructionRate = data.getDynamicObject()->getProperty("destructionRate");

  if (data.getDynamicObject()->hasProperty("freeEnergy"))
    freeEnergy = data.getDynamicObject()->getProperty("freeEnergy");

  if (data.getDynamicObject()->hasProperty("level"))
    level = data.getDynamicObject()->getProperty("level");

  if (data.getDynamicObject()->hasProperty("draw"))
    draw = data.getDynamicObject()->getProperty("draw");

  if (data.getDynamicObject()->hasProperty("composition"))
  {
    var compvar = data.getDynamicObject()->getProperty("composition");
    if (compvar.isArray())
    {
      Array<var> *comp = data.getDynamicObject()->getProperty("composition").getArray();
      for (auto &coord : *comp)
      {
        composition.add(data.getDynamicObject()->getProperty("coord"));
      }
    }
  }
}

var SimEntity::toJSONData()
{
  var data = new DynamicObject();
  data.getDynamicObject()->setProperty("name", name);
  data.getDynamicObject()->setProperty("color", color2JSON(color));
  data.getDynamicObject()->setProperty("primary", primary);
  data.getDynamicObject()->setProperty("id", id);
  data.getDynamicObject()->setProperty("concent", concent);
  data.getDynamicObject()->setProperty("startConcent", startConcent);
  data.getDynamicObject()->setProperty("creationRate", creationRate);
  data.getDynamicObject()->setProperty("destructionRate", destructionRate);
  data.getDynamicObject()->setProperty("freeEnergy", freeEnergy);
  data.getDynamicObject()->setProperty("level", level);
  data.getDynamicObject()->setProperty("draw", draw);
  var comp;
  for (auto &i : composition)
  {
    var coord = new DynamicObject();
    coord.getDynamicObject()->setProperty("coord", i);
    comp.append(coord);
  }
  data.getDynamicObject()->setProperty("composition", comp);
  return data;
}

void SimEntity::increase(float incr)
{
  concent += incr;
}

void SimEntity::decrease(float decr)
{
  concent = jmax(0.f, concent - decr);
}

void SimEntity::nameFromCompo()
{
  name = "";
  for (auto &i : composition)
  {
    name += String(i);
  }
}

String SimEntity::toString() const
{
  return "[Entity " + name + " : " + String(concent) + "]";
}

void SimEntity::importFromManual()
{
  startConcent = entity->startConcent->floatValue();
  concent = entity->concent->floatValue();
  creationRate = entity->creationRate->floatValue();
  destructionRate = entity->destructionRate->floatValue();
  freeEnergy = entity->freeEnergy->floatValue();
  enabled = entity->enabled->boolValue();
  color = entity->itemColor->getColor();
  level = entity->level;
  composition = entity->composition;
  draw = entity->draw->boolValue();
  primary = entity->primary->boolValue();
}

void SimReaction::importFromManual()
{
  assocRate = reaction->assocRate->floatValue();
  dissocRate = reaction->dissocRate->floatValue();
  energy = reaction->energy->floatValue();
  enabled = reaction->shouldIncludeInSimulation();
}

void SimReaction::setName()
{
  name = reactant1->name + "+" + reactant2->name + "=" + product->name;
}

SimReaction::SimReaction(Reaction *r) : assocRate(r->assocRate->floatValue()),
                                        dissocRate(r->dissocRate->floatValue()),
                                        energy(r->energy->floatValue()),
                                        reaction(r)
{
  r->simReac = this;
  reactant1 = (dynamic_cast<Entity *>(r->reactant1->targetContainer.get()))->simEnt;
  reactant2 = (dynamic_cast<Entity *>(r->reactant2->targetContainer.get()))->simEnt;
  product = (dynamic_cast<Entity *>(r->product->targetContainer.get()))->simEnt;
  setName();
}

SimReaction::SimReaction(SimEntity *r1, SimEntity *r2, SimEntity *p, float aRate, float dRate, float barrier) : reactant1(r1), reactant2(r2), product(p), assocRate(aRate), dissocRate(dRate), energy(barrier)
{
  setName();
}

SimReaction::SimReaction(var data)
{
  if (data.isVoid())
    return;
  if (data.getDynamicObject() == nullptr)
    return;

  Simulation *simul = Simulation::getInstance();
  if (data.getDynamicObject()->hasProperty("reactant1_id"))
    reactant1 = simul->getSimEntityForID(data["reactant1_id"]);

  reactant1 = simul->getSimEntityForID(data.getProperty("reactant1_id", -1));

  // to change on same model
  if (data.getDynamicObject()->hasProperty("reactant2_id"))
    reactant2 = simul->getSimEntityForID(data["reactant2_id"]);

  if (data.getDynamicObject()->hasProperty("product_id"))
    product = simul->getSimEntityForID(data["product_id"]);

  if (data.getDynamicObject()->hasProperty("assocRate"))
    assocRate = data["assocRate"];

  if (data.getDynamicObject()->hasProperty("dissocRate"))
    dissocRate = data["dissocRate"];

  if (data.getDynamicObject()->hasProperty("idSAT"))
    idSAT = data["idSAT"];

  setName();
}

var SimReaction::toJSONData()
{
  var data = new DynamicObject();
  data.getDynamicObject()->setProperty("reactant1_id", reactant1->id);
  data.getDynamicObject()->setProperty("reactant2_id", reactant2->id);
  data.getDynamicObject()->setProperty("product_id", product->id);

  data.getDynamicObject()->setProperty("assocRate", assocRate);
  data.getDynamicObject()->setProperty("dissocRate", dissocRate);

  data.getDynamicObject()->setProperty("idSAT", idSAT);

  return data;
}

bool SimReaction::contains(SimEntity *e)
{
  return (reactant1 == e || reactant2 == e || product == e);
}

void SimReaction::computeRate(bool noBarrier, bool noFreeEnergy)
{
  // GA+GB
  float energyLeft = noFreeEnergy ? 0.f : reactant1->freeEnergy + reactant2->freeEnergy;
  // GAB
  float energyRight = noFreeEnergy ? 0.f : product->freeEnergy;
  // total energy G* of the reaction: activation + max of GA+GB and GAB.
  float energyStar = (noBarrier ? 0.f : energy) + jmax(energyLeft, energyRight);
  // k1=exp(GA+GB-G*)
  assocRate = exp(energyLeft - energyStar);
  // k2=exp(GAB-G*)
  dissocRate = exp(energyRight - energyStar);
}

void SimReaction::computeBarrier()
{
  // compute energy barrier
  float energyLeft = reactant1->freeEnergy + reactant2->freeEnergy;
  ;
  float energyRight = product->freeEnergy;

  // we use that assocRate is exp(energyLeft - energyStar) to compute energyStar
  float energyStar = energyLeft - log(assocRate);
  // we use that energyStar = energy + jmax(energyLeft, energyRight); to compute energy
  energy = energyStar - jmax(energyLeft, energyRight);
}