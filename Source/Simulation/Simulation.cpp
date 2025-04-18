#include "Simulation.h"
#include "EntityManager.h"
#include "ReactionManager.h"
#include "Generation.h"
#include "Settings.h"
#include "Statistics.h"
#include "Util.h"

// #include <SimpleXlsxWriter.hpp> // Inclure la bibliothèque C++ Excel

using namespace std;

#define DT_PRECISION 5

juce_ImplementSingleton(Simulation)

    Simulation::Simulation() : ControllableContainer("Simulation"),
                               Thread("Simulation"),
                               curStep(0),
                               simNotifier(1000), // max messages async that can be sent at once
                               pacList(new PAClist(this)),
                               steadyStatesList(new SteadyStateslist(this))
  //                             space(new Space(this))
{
  simNotifier.dropMessageOnOverflow = false;

  dt = addFloatParameter("dt", "time step in ms", .01, 0.f);
  totalTime = addFloatParameter("Total Time", "Total simulated time in seconds", 1.f, 0.f);
  pointsDrawn = addIntParameter("Checkpoints", "Number of checkpoints to draw points and observe RACs", 100, 1);
  perCent = addIntParameter("Progress", "Percentage of the simulation done", 0, 0, 100);
  perCent->setControllableFeedbackOnly(true);
  finished = addBoolParameter("Finished", "Finished", false);
  finished->setControllableFeedbackOnly(true);
  maxConcent = addFloatParameter("Max. Concent.", "Maximal concentration displayed on the graph", 5.f);
  realTime = addBoolParameter("Real Time", "Print intermediary steps of the simulation", false);
  liveUpdate = addBoolParameter("Live Update", "Restart simulation when relevant parameters change", true);

  // loadToManualByDefault = addBoolParameter("AutoLoad to Lists", "Automatically load the current simulation to manual lists", true);
  genTrigger = addTrigger("Generate", "Generate");
  startTrigger = addTrigger("Continue", "Continue");
  genstartTrigger = addTrigger("Gen. & Start", "Gen. & Start");
  restartTrigger = addTrigger("Start", "Start");
  cancelTrigger = addTrigger("Cancel", "Cancel");
  autoScale = addBoolParameter("Auto Scale", "Automatically scale to maximal concentration reached", true);
  oneColor = addBoolParameter("Unicolor", "Use only one color for each RAC", true);
  detectEquilibrium = addBoolParameter("Detect Equil.", "Detect equilibrium and stop simulation", false);
  epsilonEq = addFloatParameter("Eps.", "Epsilon for equilibrium detection", 0.0001f, 0.f, 1.f);
  // ready = addBoolParameter("Ready","Can the simulation be launched ?", false);
  setCAC = addEnumParameter("Set CAC", "Set current concentrations according to CAC witness");
  setSteadyState = addEnumParameter("Set Steady State", "Set current concentrations to steady state");
  setRun = addEnumParameter("Set Run", "Draw concentration dynamics associated to chosen run");
  ignoreFreeEnergy = addBoolParameter("Ignore Free Energy", "Ignore free energy of entities in the simulation", false);
  ignoreBarriers = addBoolParameter("Ignore Barriers", "Ignore barrier energy of reactions in the simulation", false);
  stochasticity = addBoolParameter("Stochasticity", "Add stochasticity in the simulation dynamics", false);
  isSpace = addBoolParameter("Heterogeneous space", "Is heterogeneous space included in the simulation", false);

  
  dt->setAttributeInternal("stringDecimals", DT_PRECISION);
  maxSteps = (int)(totalTime->floatValue() / dt->floatValue());
  maxSteps = jmax(1, maxSteps);
  
  dynHistory = new DynamicsHistory();
}

Simulation::~Simulation()
{
  // Destructor
  stopThread(500);
}

// void Simulation::filterReached()
// {
//   // set primary entities to reached
//   for (auto &e : entities)
//   {
//     e->reached = false;
//     if (e->primary)
//     {
//       e->reached = true;
//     }
//   }
//   // propagate to composite ones using reactions
//   bool progress = true;
//   // create reaction table to remove used reactions
//   Array<SimReaction *> reacToCheck;
//   for (auto &r : reactions)
//   {
//     reacToCheck.add(r);
//     r->reached = false;
//   }
//   while (progress)
//   {
//     progress = false;

//     for (auto &r : reacToCheck)
//     {
//       SimEntity *r1 = r->reactant1;
//       SimEntity *r2 = r->reactant2;
//       SimEntity *p = r->product;
//       if (r1->reached && r2->reached)
//       {
//         p->reached = true;
//         progress = true;
//       }
//       if (p->reached)
//       {
//         r1->reached = true;
//         r2->reached = true;
//         progress = true;
//       }
//       if (progress)
//       {
//         r->reached = true;
//         reacToCheck.removeFirstMatchingValue(r);
//         break;
//       }
//     }
//   }

//   // remove unreached entities
//   for (int i = entities.size() - 1; i >= 0; i--)
//   {
//     if (!entities[i]->reached)
//     {
//       entities.remove(i);
//       cout << "removed entity " << i << endl;
//     }
//   }

//   // removed unreached reactions
//   for (int i = reactions.size() - 1; i >= 0; i--)
//   {
//     if (!reactions[i]->reached)
//     {
//       cout << "removed reaction " << reactions[i]->name << endl;
//       reactions.remove(i);
//     }
//   }
// }

void Simulation::clearParams()
{
  entitiesDrawn.clear();
  primEnts.clear();
  pacList->clear();
  reactions.clear();
  entities.clear();
  PACsGenerated = false;
  numLevels = -1;
  steadyStatesList->arraySteadyStates.clear();
  steadyStatesList->nGlobStable = 0;
  steadyStatesList->nPartStable = 0;
  //steadyStatesList->stableStates.clear();
  //steadyStatesList->partiallyStableStates.clear();
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

  // compute isolated entities
  computeIsolated();

  setCAC->clearOptions();
  // if (isComputing)
  // {
  //   setCAC->addOption("Computing...", -1);
  // }
  // else
  // {
  setCAC->addOption("CAC", -1, true);
  int opt = 1;
  // int nbCAC=pacList->CACs.size();
  for (auto &cac : pacList->CACs)
  // for (int i=0;i<nbCAC;i++)
  {
    setCAC->addOption(pacList->CACToString(cac), opt, false);
    // setCAC->addOption("Cac"+to_string(opt), opt,false);
    opt++;
  }

  // set steady states
  setSteadyState->clearOptions();
  setSteadyState->addOption("SteadyState", -1, true);
  for (int i = 0; i < steadyStatesList->arraySteadyStates.size(); i++)
  {
    int stateOpt = i + 1;
    setSteadyState->addOption(String(stateOpt), stateOpt, false);
  }
  
  // set runs
  setRun->clearOptions();
  setRun->addOption("Run", -1, true);
  for (int i = 0; i < PhasePlane::getInstance()->nRuns->intValue(); i++)
  {
    int stateOpt = i;
    setRun->addOption(String(stateOpt), stateOpt, false);
  }
  
  
  //}
  // update the parameters of the simulation in the UI
  simNotifier.addMessage(new SimulationEvent(SimulationEvent::UPDATEPARAMS, this));
}

// to save additional data, different from getJSONdata()
var Simulation::toJSONData()
{
  var data = new DynamicObject();
  
  // record concentration
  var vrc;
  for (int k=0; k<recordConcent.size(); k++)
  {
    var v = new DynamicObject();
    v.getDynamicObject()->setProperty("patch", k);
    v.getDynamicObject()->setProperty("concent", recordConcent[k]);
    vrc.append(v);
  }
  data.getDynamicObject()->setProperty("recordConcent", vrc);
  
  // record entity
  var vre;
  for (int k=0; k<recordEntity.size(); k++)
  {
    var v = new DynamicObject();
    v.getDynamicObject()->setProperty("patch", k);
    v.getDynamicObject()->setProperty("name", recordEntity[k]);
    vre.append(v);
  }
  data.getDynamicObject()->setProperty("recordEntity", vre);
  
  // record drawn
  var vrd;
  for (int k=0; k<recordDrawn.size(); k++)
  {
    var v = new DynamicObject();
    v.getDynamicObject()->setProperty("patch", k);
    v.getDynamicObject()->setProperty("concent", recordDrawn[k]);
    vrd.append(v);
  }
  data.getDynamicObject()->setProperty("recordDrawn", vrd);
  
  // record drawn entity
  var vrde;
  for (int k=0; k<recordDrawnEntity.size(); k++)
  {
    var v = new DynamicObject();
    v.getDynamicObject()->setProperty("patch", k);
    v.getDynamicObject()->setProperty("name", recordDrawnEntity[k]);
    vrde.append(v);
  }
  data.getDynamicObject()->setProperty("recordDrawnEntity", vrde);
  
  data.getDynamicObject()->setProperty("numLevels", numLevels);
  data.getDynamicObject()->setProperty("PACsGenerated", PACsGenerated);
  data.getDynamicObject()->setProperty("nRuns", nRuns);

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
    coord.getDynamicObject()->setProperty("ent", e->name);
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
  var pacListData = pacList->toJSONData();
  data.getDynamicObject()->setProperty("pacList", pacListData);
  
  // steady states
  //data.getDynamicObject()->setProperty("setSteadyStateTEST", setSteadyState->getValue());
  var vsst = steadyStatesList->toJSONData();
  data.getDynamicObject()->setProperty("SteadyStatesList", vsst);

  
  return data;
}

void Simulation::importJSONData(var data)
{
  clearParams();
  if (data.isVoid())
    return;
  if (data.getDynamicObject() == nullptr)
    return;

  recordConcent.resize(Space::getInstance()->nPatch);
  recordEntity.resize(Space::getInstance()->nPatch);
  recordDrawn.resize(Space::getInstance()->nPatch);
  recordDrawnEntity.resize(Space::getInstance()->nPatch);
  
  if (data.getDynamicObject()->hasProperty("recordConcent"))
  {
    if (data.getDynamicObject()->getProperty("recordConcent").isArray())
    {
      Array<var> * arrv = data.getDynamicObject()->getProperty("recordConcent").getArray();
      int c=-1;
      for (auto & v : *arrv)
      {
        c++;
        String patchid = v["patch"];
        float conc = v["concent"];
        recordConcent.set(c, conc);
      }
      
    }
  }
  
  if (data.getDynamicObject()->hasProperty("recordEntity"))
  {
    if (data.getDynamicObject()->getProperty("recordEntity").isArray())
    {
      Array<var> * arrv = data.getDynamicObject()->getProperty("recordEntity").getArray();
      int c=-1;
      for (auto & v : *arrv)
      {
        c++;
        String patchid = v["patch"];
        String name = v["name"];
        recordEntity.set(c, name);
      }
    }
  }
  
  if (data.getDynamicObject()->hasProperty("recordDrawn"))
  {
    if (data.getDynamicObject()->getProperty("recordDrawn").isArray())
    {
      Array<var> * arrv = data.getDynamicObject()->getProperty("recordDrawn").getArray();
      int c=-1;
      for (auto & v : *arrv)
      {
        c++;
        String patchid = v["patch"];
        float conc = v["concent"];
        recordDrawn.set(c, conc);
      }
      
    }
  }
  
  if (data.getDynamicObject()->hasProperty("recordDrawnEntity"))
  {
    if (data.getDynamicObject()->getProperty("recordDrawnEntity").isArray())
    {
      Array<var> * arrv = data.getDynamicObject()->getProperty("recordDrawnEntity").getArray();
      int c=-1;
      for (auto & v : *arrv)
      {
        c++;
        String patchid = v["patch"];
        String name = v["name"];
        recordDrawnEntity.set(c, name);
      }
    }
  }
  
  /*
  if (data.getDynamicObject()->hasProperty("recordConcent"))
    recordConcent = data.getDynamicObject()->getProperty("recordConcent");
  if (data.getDynamicObject()->hasProperty("recordEntity"))
    recordEntity = data.getDynamicObject()->getProperty("recordEntity");
  if (data.getDynamicObject()->hasProperty("recordDrawn"))
    recordDrawn = data.getDynamicObject()->getProperty("recordDrawn");
  */
  
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
      SimEntity *e = new SimEntity(evar);
      if (e->constructionFailed)
      {
        LOGWARNING("SimEntity construction failed, not added to list");
        delete e;
        continue;
      }
      entities.add(e);
    }
    maxSteps = (int)(totalTime->floatValue() / dt->floatValue());
    maxSteps = jmax(1, maxSteps);
  }
  
  cout << "----- will update entities from sim entities -----" << endl;
  if (Space::getInstance()->nPatch>0)
    updateUserListFromSim(0); // display what is in patch 0 by default
  cout << "--- updated entities from sim entities ---" << endl;

  
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
      SimReaction *r = new SimReaction(rvar);
      if (r->constructionFailed)
      {
        LOGWARNING("SimReaction construction failed, not added to list");
        delete r;
        continue;
      }
      reactions.add(r);
    }
  }

  // PACList
  if (data.getDynamicObject()->hasProperty("pacList"))
  {
    pacList->fromJSONData(data.getDynamicObject()->getProperty("pacList"));
  }
  
  // Steady States
  if (data.getDynamicObject()->hasProperty("SteadyStatesList"))
  {
    steadyStatesList->fromJSONData(data.getDynamicObject()->getProperty("SteadyStatesList"));
  }


  // precision
  dt->setAttributeInternal("stringDecimals", DT_PRECISION);
  Settings::getInstance()->CACRobustness->setAttributeInternal("stringDecimals", CACROB_PRECISION);
  computeBarriers();
  updateParams();
  
  /*
  cout << "***** Sim entities status  ******" << endl;
  for (auto & ent : entities)
  {
    cout << ent->name << " startConc : [" << ent->startConcent[0] << " ; " << ent->startConcent[1];
    cout << "] conc : [" << ent->concent[0] << " ; " << ent->concent[1] << "]" << endl;
  }
  cout << "*******************" << endl;
  */
}

// void Simulation::importFromManual()
//{
//   LOG("Importing from manual lists");
//   for (auto &e : entities)
//   {
//     if (e->toImport)
//     {
//       e->importFromManual();
//       e->toImport = false;
//     }
//   }
//   for (auto &r : reactions)
//   {
//     if (r->toImport)
//     {
//       r->importFromManual();
//       r->toImport = false;
//     }
//   }
//
//   updateParams();
// }

void Simulation::importCsvData(String filename)
{

  // CETTE FONCTION EST CHELOU !!!!!!!!!!!!!!!!!!!!!!!!!!!

  // juce::var dummy("kujhdsb");

  ////Genre ca c'est pas ok, ca va rajouter un parameter a chaque fois qu'on appelle la fonction.
  // Settings::getInstance()->pathToz3 = addStringParameter("Path to z3", String("path to z3 solver"), String("Dummy"));

  //// Settings::getInstance()->pathToz3->setValueInternal(dummy);
  // return;
  //// get csv file to parse
  // juce::String myfilename = Settings::getInstance()->csvFile->stringValue();
  // LOG("will parse text file : " + myfilename);

  //// clear what is in current simulation
  // clearParams();

  // ifstream file;
  // file.open(myfilename.toUTF8(), ios::in);
  // if (!file.is_open())
  //   throw std::exception("can't open excel file");

  // vector<vector<string>> database; // csv file content stored here
  // vector<string> row;
  // string line, element;

  //// start parsing the csv file
  // while (getline(file, line))
  //{

  //  // cout << line << "\n"; //print the data of the string
  //  row.clear();
  //  stringstream str(line);

  //  while (getline(str, element, ','))
  //  {
  //    while (element.find_first_of('"') != element.npos)
  //      element.erase(element.find_first_of('"'), 1); // remove '"' characters of string
  //    row.push_back(element);
  //  }
  //  database.push_back(row);
  //}

  ///*
  //  // sanity check
  //  cout << "number of lines in csv file : " << database.size() << "\n";
  //  for (unsigned int i=0; i<database.size(); i++){
  //    //LOG("printing line : " + to_string(i) + " with " << to_string(database[i].size()) + " elements");
  //    for (unsigned int j=0; j<database[i].size(); j++){
  //      cout << database[i][j] << "\t";
  //    } // end j loop
  //    cout << "\n";
  //  } // end i loop
  //*/

  //// get column index of reactants and products
  // int colr = -1;
  // int colp = -1;
  // int colstoi_r = -1;
  // int colstoi_p = -1;
  // vector<string> firstline = database[0];
  // for (unsigned int j = 0; j < firstline.size(); j++)
  //{
  //   if (firstline[j].find("Reactant_name") != firstline[j].npos)
  //     colr = j;
  //   else if (firstline[j].find("Product_name") != firstline[j].npos)
  //     colp = j;
  //   else if (firstline[j].find("Reactant_stoi") != firstline[j].npos)
  //     colstoi_r = j;
  //   else if (firstline[j].find("Product_stoi") != firstline[j].npos)
  //     colstoi_p = j;
  // }

  //// sanity check
  // if (colr < 0 || colp < 0 || colstoi_r < 0 || colstoi_p < 0)
  //   throw std::exception("csv index error");

  // unordered_map<String, SimEntity *> myentities;

  //// temporary
  ///// vector<tempReaction> tempreac;

  // int entID = 0; // id of entities

  //// loop over all reactions, skipping first element (column names)
  // for (unsigned int i = 1; i < database.size(); i++)
  //{
  //   // cout << endl;
  //   unordered_map<String, int> mreactants; // molecule name, stoechio
  //   unordered_map<String, int> mproducts;  // molecule name, stoechio

  //  // retrieve reactants stoechio coeff
  //  stringstream current_stoi(database[i][colstoi_r]);
  //  string stoi;
  //  vector<int> vstoi;
  //  while (getline(current_stoi, stoi, '_'))
  //    vstoi.push_back(atoi(stoi.c_str()));

  //  // retrieve reactants and associate them to their stoechio
  //  stringstream current_reac(database[i][colr]);
  //  string r;
  //  int cr = 0;
  //  while (getline(current_reac, r, '_'))
  //  {
  //    if (cr >= vstoi.size())
  //      throw runtime_error("mismatch between reactants and stoechio");
  //    String rbis = (string)r;
  //    mreactants[rbis] = vstoi[cr];
  //    cr++;
  //  }

  //  // retrieve products stoechio coeff
  //  stringstream current_stoi2(database[i][colstoi_p]);
  //  stoi.clear();
  //  vstoi.clear();
  //  while (getline(current_stoi2, stoi, '_'))
  //    vstoi.push_back(atoi(stoi.c_str()));

  //  // retrieve reactants and associate them to their stoechio
  //  stringstream current_prod(database[i][colp]);
  //  string p;
  //  int cp = 0;
  //  while (getline(current_prod, p, '_'))
  //  {
  //    if (cp >= vstoi.size())
  //      throw runtime_error("mismatch between products and stoechio");
  //    String pbis = (String)p;
  //    mproducts[pbis] = vstoi[cp];
  //    cp++;
  //  }

  //  // raise exception if number of reactants differs from 2 or
  //  /// if (mreactants.size()!=2) throw std::exception("csv file contains reactions with Nreactants != 2. Not supported");
  //  /// if (mproducts.size()!=1) throw std::exception("csv file contains reactions with Nproduct != 1. Not supported");

  //  /*
  //    cout << "---CHECK---\n reaction #" << i << endl;
  //    cout << "reactants : \n";
  //    for (const auto& it : mreactants){
  //           LOG(it.first << " " << it.second);
  //    }
  //    cout << "products : \n";
  //      for (const auto& it : mproducts){
  //           LOG(it.first << " " << it.second);
  //      }
  //  */

  //  // store reactants, products and current reaction into SimEntity and SimReaction objects
  //  // + add them to simulation instance
  //  Array<SimEntity *> simp; // products
  //  Array<SimEntity *> simr; // reactants

  //  // add reactants to simul->entities if not already added
  //  for (auto [mname, stoe] : mreactants)
  //  {
  //    // repeat operation according to stoechiometry of entity
  //    for (int s = 0; s < stoe; s++)
  //    {
  //      // add entity to simr
  //      // SimEntity * mye = new SimEntity(false, 1., 0., 0., 0.);  // use dumb value at initialization for the moment
  //      // mye->name = mmane;
  //      // simr.add(mye);

  //      // check whether current entity has already been added to simulation entity array
  //      bool alreadyAdded2Sim = false;
  //      for (auto &e : entities)
  //      {
  //        if (e->name == mname)
  //        {
  //          alreadyAdded2Sim = true;
  //          simr.add(e);
  //          break;
  //        }
  //      }

  //      if (!alreadyAdded2Sim) // if current entity was not already stored, init a new one
  //      {
  //        SimEntity *mye = new SimEntity(false, 1., 0., 0., 0.); // use dumb value at initialization for the moment
  //        mye->name = mname;
  //        mye->id = entID;
  //        mye->idSAT = entID;
  //        simr.add(mye);
  //        entities.add(mye);
  //        entID++;
  //      }

  //    } // end stoechiometry loop
  //  } // end loop over reactants

  //  // add products to simul->entities if not already added
  //  //  for (it = mproducts.begin(); it != mproducts.end(); it++)
  //  for (auto [mname, stoe] : mproducts)
  //  {
  //    for (int s = 0; s < stoe; s++)
  //    {
  //      // add entity to simp
  //      // SimEntity * mye = new SimEntity(false, 1., 0., 0., 0.);  // use dumb value at initialization for the moment
  //      // mye->name = mname;
  //      // simp.add(mye);

  //      bool alreadyAdded2Sim = false;
  //      for (auto &e : entities)
  //      {
  //        if (e->name == mname)
  //        {
  //          alreadyAdded2Sim = true;
  //          simp.add(e);
  //          break;
  //        }
  //      }

  //      if (!alreadyAdded2Sim) // if current entity was not already stored, init a new one
  //      {
  //        SimEntity *mye = new SimEntity(false, 1., 0., 0., 0.); // use dumb value at initialization for the moment
  //        mye->name = mname;
  //        mye->id = entID;
  //        mye->idSAT = entID;
  //        simp.add(mye);
  //        entities.add(mye);
  //        entID++;
  //      } // end if

  //    } // end stoechio loop
  //  } // end loop over products

  //  // check
  //  // for (const auto& r: simr){std::cout << "reactant name : " << r->name << std::endl;}
  //  // for (const auto& p: simp){std::cout << "product name : " << p->name << std::endl;}

  //  // add the current reaction to simul->reactions
  //  SimReaction *reac = new SimReaction(simr, simp, 1., 1.); // use dumb rate values
  //  reac->isReversible = false;
  //  reactions.add(reac);

  //} // end reaction loop

  //// check for reversible reactions stored as two separate reactions
  // SearchReversibleReactionsInCsvFile();

  //// sanity check
  ///*
  // for (const auto& r : reactions)
  //   {
  //   cout << "adding reaction name " << r->name << endl;
  //   for (auto& e: r->reactants) cout << "\thas reactant " << e->idSAT << endl;
  //   for (auto& e: r->products) cout << "\thas product " << e->idSAT << endl;
  //   }
  //*/

  // ready = true;
  // updateParams();

  //// directly import SimReactions and SimEntities as reaction and entity lists
  //// into the graphics interface
  // loadToManualMode();
}

// struct tempReaction // TO REMOVE, only temporary
//  {
//    vector<pair<SimEntity*, int>> reactants;
//    vector<pair<SimEntity*, int>> products;
//  };

void Simulation::SearchReversibleReactionsInCsvFile()
{
  LOG("Initial composition : " + to_string(entities.size()) + " entites & " + to_string(reactions.size()) + " reactions.");

  // reactions index that were found to match
  unordered_map<int, int> mr; // matches by convention i2 with i1 (with i2>i1), i.e mr[i2] = i1
  // index of reversible reactions
  unordered_map<int, int> rr; // reversible reactions, containing only i1 as keys

  // loop over reactions
  for (int ia = 0; ia < reactions.size(); ia++)
  {
    if (mr.count(ia) > 0)
      continue; // skip a reaction that already got a match
    SimReaction *ra = reactions[ia];

    // std::cout << "Looking at reaction " << ra->name << std::endl;

    // loop over reactions greater than current one
    for (int ib = ia + 1; ib < reactions.size(); ib++)
    {
      if (mr.count(ib) > 0)
        continue; // skip a reaction that already got a match
      SimReaction *rb = reactions[ib];

      // first trivial condition to check if both reactions have the same number of reactants & products
      if ((ra->reactants.size() != rb->products.size()) || (rb->reactants.size() != ra->products.size()))
        continue;

      // if condition above not reached, then Na(reactants) = Nb(products) and vice versa

      // get reactants & products names into vectors of strings
      StringArray astr_r, astr_p, bstr_r, bstr_p;
      for (int k = 0; k < ra->reactants.size(); k++)
        astr_r.add(ra->reactants[k]->name);
      for (int k = 0; k < ra->products.size(); k++)
        astr_p.add(ra->products[k]->name);
      for (int k = 0; k < rb->reactants.size(); k++)
        bstr_r.add(rb->reactants[k]->name);
      for (int k = 0; k < rb->products.size(); k++)
        bstr_p.add(rb->products[k]->name);

      // sort vectors of strings to allow for a direct comparison
      std::sort(astr_r.begin(), astr_r.end());
      std::sort(astr_p.begin(), astr_p.end());
      std::sort(bstr_r.begin(), bstr_r.end());
      std::sort(bstr_p.begin(), bstr_p.end());

      bool doesMatch = true;
      // compare reactants of Ra with products of Rb
      for (int k = 0; k < astr_r.size(); k++)
      {
        if (!astr_r[k].equalsIgnoreCase(bstr_p[k]))
        {
          doesMatch = false;
          break;
        }
      }
      if (!doesMatch)
        continue; // move to next reaction

      // compare products of Ra with reactants of Rb
      for (int k = 0; k < astr_p.size(); k++)
      {
        if (!astr_p[k].equalsIgnoreCase(bstr_r[k]))
        {
          doesMatch = false;
          break;
        }
      }
      if (!doesMatch)
        continue; // move to next reaction

      // std::cout << "Found match r" << ia << " <--> " << ib << std::endl;
      //  If made it up to here, then Rb should be the reverse reaction of Ra
      mr[ib] = ia;
      rr[ia]++;
      break;
    } // end ib loop
  } // end ia loop

  /*
  cout << "SearchReversibleReactionsInCsvFile:: Matching " << reactions.size() << " reactions." << endl;
  cout << "SearchReversibleReactionsInCsvFile:: found " << mr.size() << " matches." << std::endl;
  for (auto & [key, value]: mr)
  {
    std::cout << "Reactions r" << value+1 << " <--> r" << key+1 << std::endl;
  }
  */

  // remove reverse reactions + update booleen of reversible reactions
  int nrm = 0; // keep track of reactions removed for a correct indexing
  unsigned int nreac = reactions.size();
  for (unsigned int i = 0; i < nreac; i++)
  {
    // if current reaction is reverse of another one, remove it
    if (mr.count(i) > 0)
    {
      reactions.remove(i - nrm);
      nrm++;
    }
    // if current reaction has a reverse one, add it and update its isReversible value
    if (rr.count(i) > 0)
    {
      reactions[i - nrm]->isReversible = true;
    }
  } // end loop

  /*
  // sanity check
  cout << "Sanity Check:: new size = " << reactions.size() << endl;
  cout << "--- Irreversible reactions information ---" << endl;
  int nirr=0;
  for (auto& r : reactions)
  {
    if (r->isReversible){ cout << r->name << endl; nirr++;}
  }
  cout << "SearchReversibleReactionsInCsvFile:: Has " << reactions.size() << " reactions, with " << nirr << " irreversible" << endl;
  */

  // basic printings
  LOG("Final composition : " + to_string(entities.size()) + " entites & " + to_string(reactions.size()) + " reactions.");
}

bool Simulation::getUserListMode()
{
  return !express && Settings::getInstance()->userListMode->boolValue();
}

void Simulation::affectSATIds()
{
  // entities
  int i = 0;
  for (auto &e : entities)
  {
    e->idSAT = i;
    i++;
  }

  // reactions
  int j = 0;
  for (auto &r : reactions)
  {
    r->idSAT = j;
    j++;
  }
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

// void Simulation::fetchManual()
//{
//   clearParams();
//   for (auto &e : EntityManager::getInstance()->items)
//   {
//     if (!e->enabled->boolValue())
//       continue;
//     auto se = new SimEntity(e);
//     entities.add(se);
//   }
//
//   for (auto &r : ReactionManager::getInstance()->items)
//   {
//     if (!r->shouldIncludeInSimulation())
//       continue;
//     reactions.add(new SimReaction(r));
//   }
//
//   // todo compute levels and primary entities
//
//   ready = true;
//   updateParams();
// }

// link entities and simEntities via their names
// void Simulation::establishLinks()
//{
//  bool found;
//  for (auto &e : EntityManager::getInstance()->items)
//  {
//    if (!e->enabled->boolValue())
//      continue;
//    found = false;
//    for (auto &se : entities)
//    {
//      if (se->name == e->niceName)
//      {
//        se->entity = e;
//        e->simEnt = se;
//        found = true;
//        break;
//      }
//    }
//    if (!found)
//    {
//      LOGWARNING("Entity " << e->niceName << " not found in simulation");
//    }
//  }
//
//  // same with reactions
//  for (auto &r : ReactionManager::getInstance()->items)
//  {
//    if (!r->shouldIncludeInSimulation())
//      continue;
//    r->simReac = nullptr;
//    found = false;
//    for (auto &sr : reactions)
//    {
//      if (sr->name == r->niceName)
//      {
//        sr->reaction = r;
//        r->simReac = sr;
//        found = true;
//        break;
//      }
//    }
//
//    if (r->reactants->controllables.size() == 0 || r->products->controllables.size() == 0)
//    {
//      // LOG("Reaction " + r->niceName + " has " + String(r->reactants->controllables.size()) + " reactants and " + String(r->products->controllables.size()) + " products.");
//
//      r->clearReactants();
//      r->clearProducts();
//
//      // creates a bug for now, to understand...
//
//      auto sr = r->simReac;
//      if (sr == nullptr)
//      {
//        LOG("SimReaction not found for reaction " + r->niceName);
//        continue;
//      }
//      for (auto &se : sr->reactants)
//      {
//        r->addReactant(se->entity);
//      }
//      for (auto &se : sr->products)
//      {
//        r->addProduct(se->entity);
//      }
//    }
//    if (!found)
//    {
//      LOGWARNING("Reaction " << r->niceName << " not found in simulation");
//    }
//  }
//}

void Simulation::computeIsolated()
{
  // Find isolated entities
  for (auto &e : entities)
  {
    e->isolated = true;
    for (auto &r : reactions)
    {
      if (r->contains(e))
      {
        e->isolated = false;
        break;
      }
    }
  }
}


void Simulation::updateUserListFromSim(int patchid)
{
  // clear previous  (beware of the order !)

  // filter array to retrieve only disabled ones

  // load entities
  for (auto &se : entities)
  {
    if (Entity *e = EntityManager::getInstance()->getItemWithName(se->name, true))
    {
      e->simEnt = se;
      e->startConcent->setValue(se->startConcent[patchid]);
      e->concent->setValue(se->concent[patchid]);
    }
    else
    {
      LOGWARNING("Sim Entity " << se->name << " not found in entity manager, this should not happen in user list mode");
    }
  }
}


void Simulation::fetchGenerate()
{
  clearParams();

  state = Generating;

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
    e->toImport = false;
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

  genMode mode = CONSTANT;
  Generation::GrowthMode gm = gen->growthEntitiesPerLevel->getValueDataAsEnum<Generation::GrowthMode>();
  switch (gm)
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

  default:
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
            // NLOG("Compos","New "<<ent1->name<< " + "<<ent2->name);
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

      // we are looping through possible rections to create the entity e
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

          // NLOG("New reaction",reac->name << " with assoc rate " << reac->assocRate << " and dissoc rate " << reac->dissocRate);
          reactions.add(reac);

          // NLOG("New reaction", e->name << " = " << e1->name << " + " << e2->name);
          nbReacDone++;
        }
        // remove this decomposition
        compos[idComp]->decomps.remove(idDecomp);
        if (nbReacDone == nbReac && mode != PROPREACTIONS) // ignore nbReac if mode is PROPREACTIONS
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
  // ready = true;

  // filter unreached entities and reactions
  // filterReached();

  LOG("Generated " << entities.size() << " entities and " << reactions.size() << " reactions");
  updateParams();

  if (getUserListMode())
  {
    Array<UndoableAction *> clearActions;
    Array<Reaction *> oldReactions;
    oldReactions.addArray(ReactionManager::getInstance()->items.getRawDataPointer(), ReactionManager::getInstance()->items.size());
    clearActions.addArray(ReactionManager::getInstance()->getRemoveItemsUndoableAction(oldReactions));

    Array<Entity *> oldEntities;
    oldEntities.addArray(EntityManager::getInstance()->items.getRawDataPointer(), EntityManager::getInstance()->items.size());
    clearActions.addArray(EntityManager::getInstance()->getRemoveItemsUndoableAction(oldEntities));

    UndoMaster::getInstance()->performActions("Clear old entity and reaction lists", clearActions);

    Array<Entity *> newItems;
    for (auto &e : entities)
      newItems.add(new Entity(e, 0));
      //newItems.add(new Entity(e));
    UndoMaster::getInstance()->performAction("Generate new entity list", EntityManager::getInstance()->getAddItemsUndoableAction(newItems));

    // same for reactions
    Array<Reaction *> newReactions;
    for (auto &r : reactions)
      newReactions.add(new Reaction(r));
    UndoMaster::getInstance()->performAction("Generate new reaction list", ReactionManager::getInstance()->getAddItemsUndoableAction(newReactions));
    
    // update phase plane entity list
    /*
    Array<Run *> newRuns;
    //for (auto &ent : entities)
    for (int irun=0; irun<2; irun++)
    {
      String name = "run " + String(to_string(irun));
      newRuns.add(new Run(name));
    }
    */
    //UndoMaster::getInstance()->performAction("Generate new run list", RunManager::getInstance()->getAddItemsUndoableAction(newRuns));
    
    //PhasePlane::getInstance()->updateEntitiesInRuns();
    
  }

  // if (Settings::getInstance()->autoLoadLists->boolValue() && !express)
  //   loadToManualMode();
}

void Simulation::generateSimFromUserList() 
{
  state = Generating;

  EntityManager *em = EntityManager::getInstance();
  ReactionManager *rm = ReactionManager::getInstance();

  // entities.clear();
  // reactions.clear();

  // disable all entities before adding them back from user list
  for (auto &e : entities)
  {
    e->generatedFromUserList = false;
  }

  // entities
  for (auto &e : em->items)
  {
    if(e->simEnt) //if a simEntity is already registered, we update it
    {
      e->simEnt->updateFromEntity(e);
      continue;
    }
    // if there is a simEntity with same name, we update it
    if (SimEntity *se = getSimEntityForName(e->niceName))
    {
      //register the link
      if (se->entity != e)
      {
        if (se->entity)
        {
          LOGWARNING("SimEntity " << se->name << " rerouted from Entity" << se->entity->niceName << " to " << e->niceName);
        }
        else
        {
          LOGWARNING("SimEntity " << se->name << " was linked to no entity, rerouted to Entity" << e->niceName);
        }
      }
      se->updateFromEntity(e);
      continue;
    }
    // else add it
    auto se = new SimEntity(e);
    entities.add(se);
    LOG("Added entity " << se->name << " to simulation");
  }



  // reactions
  // disable all reactions before adding them back from user list
  for (auto &r : reactions)
  {
    r->generatedFromUserList = false;
  }

  for (auto &r : rm->items)
  {
    if (!r->shouldIncludeInSimulation())
      continue;

    // if there is a simReaction with same name, we update it
    if (SimReaction *sr = getSimReactionForName(r->niceName))
    {
      if (sr->reaction != r)
      {
        if (sr->reaction)
        {
          LOGWARNING("SimReaction " << sr->name << " rerouted from Reaction" << sr->reaction->niceName << " to " << r->niceName);
        }
        else
        {
          LOGWARNING("SimReaction " << sr->name << " was linked to no reaction, rerouted to Reaction" << r->niceName);
        }
      }
      sr->updateFromReaction(r);
      continue;
    }
    // else add it
    reactions.add(new SimReaction(r));
  }

//update PACs by removing those with reactions not in the user list
  for (int i = pacList->cycles.size() - 1; i >= 0; i--)
  {
    auto pac = pacList->cycles[i];
    for(auto &rd : pac->reacDirs)
    {
      if (!rd.first || !rd.first->generatedFromUserList)
      {
        pacList->removePAC(i);
        break;
      }
    }
  }


  // remove reactions that are not in the user list
  for (int i = reactions.size() - 1; i >= 0; i--)
  {
    if (!reactions[i]->generatedFromUserList)
    {
      reactions.remove(i);
    }
  }

    // remove entities that are not in the user list
  for (int i = entities.size() - 1; i >= 0; i--)
  {
    if (!entities[i]->generatedFromUserList)
    {
      entities.remove(i);
    }
  }

  LOG("Generated Simulation entities and reactions from user list");
  state=Idle;
  updateParams();
}




void Simulation::resetBeforeRunning()
{
  stopThread(100);
  startTrigger->setEnabled(false);
  state = Simulating;
  isMultipleRun = false;
  
  initialConcentrations.clear();
  for (auto& ent: entities)
    ent->concentHistory.clear();
  RAChistory.clear();

  currentRun = 0;
  recordConcent.resize(Space::getInstance()->nPatch);
  recordDrawn.resize(Space::getInstance()->nPatch);
  for (int k=0; k<Space::getInstance()->nPatch; k++)
  {
    recordConcent.set(k, 0.);
    recordDrawn.set(k, 0.);
  }
  
  if (isMultipleRun)
    runToDraw = nRuns-1;
  else
    runToDraw = 0;
  patchToDraw = 0;
  //recordDrawn = 0.;
  checkPoint = maxSteps / pointsDrawn->intValue(); // draw once every "chekpoints" steps
  checkPoint = jmax(1, checkPoint);
  
  //cout << "checkpoint being reset at maxSteps / pointsdrawn = " << maxSteps << " / " << pointsDrawn->intValue() << " = " << checkPoint << endl;
  
  setRun->setValue(0);
  
  if (stochasticity->boolValue())
  {
    rgg = new RandomGausGenerator(0., 1.); // init random generator
    rgg->generator->seed(std::chrono::system_clock::now().time_since_epoch().count());
    noiseEpsilon = Settings::getInstance()->epsilonNoise->floatValue();
    if (Settings::getInstance()->fixedSeed->boolValue()==true)
    {
      // check that the seed string has correct format, i.e. only digits
      string strSeed = string(Settings::getInstance()->randomSeed->stringValue().toUTF8());
      bool correctFormat = true;
      for (int k=0; k<strSeed.size(); k++)
      {
        if (!isdigit(strSeed[k]))
        {
          correctFormat = false;
          break;
        }
      }
      if (!correctFormat)
      {
        LOGWARNING("Incorrect random seed format, should contain only digits. Seed set to 1234 instead");
      }
      else
      {
        unsigned int seed = atoi(strSeed.c_str());
        rgg->setFixedSeed(seed);
      }
    }
  }
  
  
  // clear space grid
  //spaceGrid.clear();
  // clear history dynamics before throwing new simulation
  dynHistory->concentHistory.clear();
  dynHistory->racHistory.clear();
  
  
  // following will be #obsolete at some point and replaced by the two command lines above
  
  //cout << "in reset nruns = " << PhasePlane::getInstance()->nRuns->intValue() << endl;
  //for (int irun=0; irun<PhasePlane::getInstance()->nRuns->intValue(); irun++)
  for (int irun=0; irun<nRuns; irun++)
  {
    auto* row = new juce::OwnedArray<RACHist>();
    for (auto &pac : pacList->cycles)
    {
      //RAChistory[irun]->add(new RACHist(pac->entities, pac->score));
      row->add(new RACHist(pac->entities, pac->score));
    }
    //unique_ptr<OwnedArray<RACHist>> urh = rh;
    RAChistory.add(row);
  }
  //cout << "in reset RAChist size on run axis : " << RAChistory.size() << endl;
  
}




void Simulation::start(bool restart)
{
  nRuns = 1;
  resetBeforeRunning();
  updateParams();
  
  
  if (isMultipleRun && isSpace->boolValue())
  {
    LOG("Cannot handle multiple run mode in heterogeneous space for now. Stop.");
    return;
  }
  
  // if (!ready)
  //{
  //	LOGWARNING("No simulation loaded, using manual lists");
  //	//fetchManual();
  // }
  // else
  //{
  //	//if (!express)
  //		//importFromManual(); // import entities and reactions from manual lists, only those who have been changed
  // }

  if (getUserListMode())
  {
    // generateSimFromUserList();
  }
  else
  {
    if (entities.isEmpty())
    {
      LOGWARNING("No entity defined, generating some");
      fetchGenerate();
    }
    else if (reactions.isEmpty())
    {
      LOGWARNING("Launching simulation with no reaction. This will be boring. Or not.");
    }
  }

  // warn here
  if (getUserListMode())
  {
    for (auto &r : ReactionManager::getInstance()->items)
    {
      r->updateWarnAndRates();
    }
  }

  if (restart)
  {
    for (auto &e : entities)
    {
      e->concent = e->startConcent;
      e->deterministicConcent = e->startConcent;
    }
  }

  // computeRates(); // compute reactions rates to take into account the ignored energies

  // 1st call of simulation event
  if (!express)
    simNotifier.addMessage(new SimulationEvent(SimulationEvent::WILL_START, this));
  // init simulation event
  Array<float> entityValues;
  Array<Colour> entityColors;
  for (auto &ent : entitiesDrawn)
  {
    //entityValues.add(ent->concent);
    entityValues.add(ent->concent[0]);
    entityColors.add(ent->color);
  }
  
  if (!express)
    simNotifier.addMessage(new SimulationEvent(SimulationEvent::STARTED, this, 0, entityValues, entityColors));
  // listeners.call(&SimulationListener::simulationStarted, this);
  
    
  // We keep track of dynamics in multipleRun and space mode to be able to redraw the dynamics for a given patch/run
  if (isMultipleRun || isSpace->boolValue() || Settings::getInstance()->printHistoryToFile->boolValue())
  {
    for (auto & patch : Space::getInstance()->spaceGrid)
    {
      ConcentrationSnapshot concsnap;
      concsnap.step = 0;
      concsnap.runID = 0;
      concsnap.patchID = patch.id;
      for (auto & ent : entities)
      {
        concsnap.conc[ent] = ent->concent[patch.id];
      }
      dynHistory->concentHistory.add(concsnap);
      // add null rac snapshots for each PAC
      for (int k=0; k<pacList->cycles.size(); k++)
      {
        Array<float> nullflows(pacList->cycles[k]->entities.size());
        for (int j=0; j<nullflows.size(); j++)
          nullflows.set(j, 0.);
        RACSnapshot rs(0., nullflows);
        rs.racID = k;
        rs.step = 0;
        rs.patchID = patch.id;
        rs.runID = 0;
        dynHistory->racHistory.add(rs);
      }
    }
  }

  
  // update maxConc encountered with initial values
  for (auto & patch : Space::getInstance()->spaceGrid)
  {
    for (auto & ent : entities)
    {
      if (ent->concent[patch.id] > recordConcent[patch.id])
      {
        recordConcent.set(patch.id, ent->concent[patch.id]);
        if (ent->draw)
          recordDrawn.set(patch.id, ent->concent[patch.id]);
      }
    }
  }
  

  // remove RACs
  for (auto &pac : pacList->cycles)
  {
    pac->wasRAC = false;
  }
  pacList->maxRAC = 0.;
  

///  RAChistory.clear();
///  for (auto &pac : pacList->cycles)
///  {
///    RAChistory.add(new RACHist(pac->entities, pac->score));
///  }
///  checkPoint = maxSteps / pointsDrawn->intValue(); // draw once every "chekpoints" steps
///  checkPoint = jmax(1, checkPoint);
 
  startThread();
}



void Simulation::startMultipleRuns(Array<map<String, float>> initConc)
{
  
  nRuns = PhasePlane::getInstance()->nRuns->intValue();
  updateParams();
  resetBeforeRunning();
  initialConcentrations = initConc;
  isMultipleRun = true;
  setRun->setValue(nRuns-1);
  
  if (isMultipleRun && isSpace->boolValue())
  {
    LOG("Cannot handle multiple run mode in heterogeneous space for now. Stop.");
    return;
  }

  
  // will print dynamics to file
  //if (!Settings::getInstance()->printHistoryToFile->boolValue())
  //  Settings::getInstance()->printHistoryToFile->setValue(true);
  
  // 1st call of simulation event
  if (!express)
    simNotifier.addMessage(new SimulationEvent(SimulationEvent::WILL_START, this));
  // Init simulation event with initial conditions of the last run
  Array<float> entityValues;
  Array<Colour> entityColors;
  for (auto &ent : entitiesDrawn)
  {
    entityValues.add(initConc[initConc.size()-1][ent->name]);
    entityColors.add(ent->color);
  }
  if (!express)
    simNotifier.addMessage(new SimulationEvent(SimulationEvent::STARTED, this, 0, entityValues, entityColors));
  
  // init max concentrations with initial conditions of last run
  map<String, float> lastrun = initConc[initConc.size()-1];
  LOGWARNING("TODO ! The piece of code executed below needs to be thought more carefully, because it requires space and multiple run to be able to run together.");
  for (auto & [name, conc] : lastrun) // init with last run
  {
    if (conc > recordConcent[0])
    {
      recordConcent.set(0, conc);
      if (getSimEntityForName(name)->draw)
        recordDrawn.set(0, conc);
    }
  }
  
  // init concentrations of sim entities to the one of the first run
  if (initConc.size()==0) return;
  for (auto & [entname, startconc] : initialConcentrations[0])
  {
    SimEntity * se = getSimEntityForName(entname);
    if (se)
    {
      se->concent.set(0, startconc);
      se->deterministicConcent.set(0, startconc);
    }
    else
    {
      LOG("couldn't retrieve sim entity with name " + entname + ". Cancel multiple run thread.");
    }
  }
  
  
  startThread();
  return;
  
}


void Simulation::nextRedrawStep(ConcentrationSnapshot concSnap, Array<RACSnapshot> racSnaps)
{
  
  nSteps++;
  bool isCheckForRedraw = ( (nSteps-1) % checkPoint == 0);
  
  
  //cout << "nsteps = " << nSteps << endl;
  //cout << pointsDrawn->intValue() << endl;
  //cout << "ischeck for redraw : " << isCheckForRedraw << endl;
  
  if (!isCheckForRedraw)
    return;
  
  
    //int idrun = setRun->intValue();
   // int istep = (nSteps-1) + idrun*maxSteps;
    //int firststep = idrun*maxSteps;
    //int laststep = maxSteps+maxSteps*idrun-1;
    
    
    //if (istep>=laststep)
    if (nSteps>maxSteps)
    {
      stop();
      return;
    }
    
    Array<float> concarray;
    Array<Colour> entityColours;
    int ident=-1;
    
    // recover drawn entity concentrations and colors
    for (auto & ent : entities)
    {
      ident++;
      if (!ent->draw)
        continue;
      entityColours.add(ent->color);
      //float entconc = ent->concentHistory[istep].second;
      float c = concSnap.conc[ent];
      concarray.add(c);
      if (c > recordDrawn[patchToDraw])
        recordDrawn.set(patchToDraw, c);
      //cout << "istep : " << istep << " on " << ent->concentHistory.size() << endl;
    }
    
    if (racSnaps.size() != pacList->cycles.size())
    {
     // cout << "racsnap size : " << racSnaps.size() << " VS pac cycle size : " << pacList->cycles.size() << endl;
      LOG("array size issue when redrawin RACs, stop.");
      stop();
      return;
    }
    
    // recover RACs values
    Array<float> racarray(racSnaps.size());
    for (int k=0; k<racSnaps.size(); k++)
    {
      //cout << "setting : " << racSnaps.getUnchecked(k).racID << endl;
      racarray.set(racSnaps.getUnchecked(k).racID, racSnaps.getUnchecked(k).rac);
    }
  
    Array<bool> raclist(pacList->cycles.size());
    for (int ipac=0; ipac<pacList->cycles.size(); ipac++)
    {
      bool wasrac = dynHistory->wasRAC[pacList->cycles[ipac]];
      raclist.set(ipac, wasrac);
    }
    
    
    if (curStep==0)
    {
      simNotifier.addMessage(new SimulationEvent(SimulationEvent::STARTED, this, curStep, concarray, entityColours, racarray, raclist));
      simNotifier.addMessage(new SimulationEvent(SimulationEvent::NEWSTEP, this, curStep, concarray, {}, racarray, raclist));
    }
    else
    {
      //cout << "Calling new SimNotifier in redraw" << endl;
      simNotifier.addMessage(new SimulationEvent(SimulationEvent::NEWSTEP, this, curStep, concarray, {}, racarray, raclist));
    }
  
  
  curStep++;
  
}




void Simulation::nextStep()
{

  nSteps++;
  
  // if multiple runs mode, decide whether to start a new run
  // I should put all of that in a function #TODO
  if (isMultipleRun)
  {
    if (nSteps>maxSteps) // current run is over
    {
      if (currentRun<(nRuns-1)) // should start new run
      {
        currentRun++;
        nSteps = 0; // re-initialize step counter
        // reset concentrations to next run initial conditions
        for (auto & [name, startconc] : initialConcentrations[currentRun])
        {
        //  cout << "[" << name << "] = " << startconc << endl;
          getSimEntityForName(name)->concent = startconc;
          getSimEntityForName(name)->deterministicConcent = startconc;
        }
        
        if (!express)
          simNotifier.addMessage(new SimulationEvent(SimulationEvent::WILL_START, this, currentRun));
        Array<float> entityValues;
        Array<Colour> entityColors;
        for (auto &ent : entitiesDrawn)
        {
          entityValues.add(initialConcentrations[initialConcentrations.size()-1][ent->name]);
          entityColors.add(ent->color);
        }
        
        //if (!express && currentRun == (nRuns-1))
        //  simNotifier.addMessage(new SimulationEvent(SimulationEvent::STARTED, this, 0, entityValues, entityColors));
        
        // reset records
        for (int k=0; k<Space::getInstance()->nPatch; k++)
        {
          recordConcent.set(k, 0.);
          recordDrawn.set(k, 0.);
        }
        
        map<String, float> lastrun = initialConcentrations[initialConcentrations.size()-1];
        for (auto & patch : Space::getInstance()->spaceGrid)
        {
          for (auto & [name, conc] : lastrun) // init with last run
          {
            if (conc > recordConcent[patch.id])
            {
              recordConcent.set(patch.id, conc);
              if (getSimEntityForName(name)->draw)
                recordDrawn.set(patch.id, conc);
            }
          }
        }
      }
      else // stop simulation
      {
        stop();
      }
      return;
    }
  }
  else
  {
    if (curStep >= maxSteps && !express) // in express mode we wait for the equilibrium
    {
      stop();
      return;
    }
  }
  
  
  bool isCheck = (curStep % checkPoint == 0);

  if (displayLog && isCheck)
  {
    LOG("New Step : " << curStep);
    wait(1);
  }
  

  // Start a loop over patches and calculate all reaction reactions rates
  for (auto & patch : Space::getInstance()->spaceGrid)
    updateSinglePatchRates(patch, isCheck);
  
  // refresh entity concentrations
  float maxVar = 0.;
  for (auto &ent : entities)
  {
    // update concentration
    ent->refresh();
    
    // sanity check
    for (auto & patch : Space::getInstance()->spaceGrid)
    {
      if (isinf(ent->concent[patch.id])) // à adapter
      {
        string coord = "(" + to_string(patch.rowIndex) + " ; " + to_string(patch.colIndex) + ")";
        LOG("Concentration of entity " << ent->name << " exceeded capacity in patch with coordinates " + String(coord));
        finished->setValue(true);
        return;
      }
    }
    
    
    
    // keep this here, but loop over patches
    float variation = abs(ent->concent[0] - ent->previousConcent[0]);
    maxVar = jmax(maxVar, variation);
  }
  maxVarSpeed = maxVar / dt->floatValue();

  
  
  // increment step value and progress bar
  curStep++;
  if (nRuns>0)
    perCent->setValue((int)((curStep * 100) / (maxSteps*nRuns)));
  

  // save a snapshot of concentrations in patches
  for (auto & patch : Space::getInstance()->spaceGrid)
  {
  
    ConcentrationSnapshot concsnap;
    concsnap.step = curStep;
    concsnap.runID = currentRun;
    concsnap.patchID = patch.id;
    
    for (auto &ent : entities)
    {
      if ( (ent->concent[patch.id] > recordConcent[patch.id]) && currentRun==(nRuns-1)) // should be only in the isCheck case
      {
        recordConcent.set(patch.id, ent->concent[patch.id]);
        recordEntity.set(patch.id, ent->name);
      }
      
      // same
      //if (ent->draw && ent->concent > recordDrawn)
      if (ent->draw && ent->concent[patch.id] > recordDrawn[patch.id] && currentRun==(nRuns-1)) // same
      {
        recordDrawn.set(patch.id, ent->concent[patch.id]);
        recordDrawnEntity.set(patch.id, ent->name);
      }
      
      // same
      if (displayLog)
      {
        for (auto &e : entities)
        {
          if (e->draw && displayLog)
            LOG(e->toString());
        }
      }
      
      // We keep track of dynamics in multipleRun and space mode to be able to redraw the dynamics for a given patch/run
      if (isCheck || isMultipleRun || isSpace->boolValue() || Settings::getInstance()->printHistoryToFile->boolValue())
      {
        concsnap.conc[ent] = ent->concent[patch.id];
      }
  
    }
    if (isCheck || isMultipleRun || isSpace->boolValue() || Settings::getInstance()->printHistoryToFile->boolValue())
    {
      dynHistory->concentHistory.add(concsnap);
    }
      
    
  } // end space grid loop
  
    
  // stop the simulation when steady state is reached in express mode or if detectEquilibrium is true
  if (detectEquilibrium->boolValue() || express)
  {
    bool reachedSteadystate = true;
    for (auto & patch : Space::getInstance()->spaceGrid)
    {
      if (maxVarSpeed[patch.id] > epsilonEq->floatValue())
      {
        reachedSteadystate = false;
        break;
      }
    }

    if (reachedSteadystate && !isMultipleRun)
    {
      if (!express)
      {
        float max = *std::max_element(maxVarSpeed.begin(), maxVarSpeed.end());
        LOG("Equilibrium reached after time " << curStep * dt->floatValue() << " s with max speed " << max);
      }
      stop();
    }
  }
  
  // rest only to call only pointsDrawn time
  if (!isCheck && !isMultipleRun && Space::getInstance()->nPatch==1)
    return;
    
  // for now we don't care about RACs in express mode
  if (express)
    return; 
    
  // storing current concentrations (patch 0) for drawing
  Array<float> entityValues;
  for (auto &ent : entitiesDrawn)
  {
    entityValues.add(ent->concent[0]);
  }


  // compute RACs. #TODO REFACTO --> move to new function
  for (auto & patch : Space::getInstance()->spaceGrid)
  {
    int idPAC = 0;
    for (auto &cycle : pacList->cycles)
    {
      idPAC++;
      // compute the total cycle flow for each entity of the PAC
      map<SimEntity *, float> flowPerEnt;
      for (auto &ent : entities)
        flowPerEnt[ent] = 0.;
      for (auto &reacDir : cycle->reacDirs)
      {
        SimReaction *reac = reacDir.first;
        
        // no need for dir, it is encoded in the sign of the flow
        // reactant/product is encoded in stoichiometry value
        for (auto &ent : reac->reactants)
        {
          flowPerEnt[ent] -= reac->deterministicFlow[patch.id]; // using deterministic trajectories to avoid "noisy" RAC plots
        }
        for (auto &ent : reac->products)
        {
          flowPerEnt[ent] += reac->deterministicFlow[patch.id];
        }
      }
      
      // compute the flow of the cycle: the minimum of the flow of each entity, or 0 if negative
      cycle->flow.set(patch.id, flowPerEnt[cycle->entities[0]]); // initialisation to a potential value, either <=0 or bigger than real value
      cycle->activity.set(patch.id, 0.);
      for (auto &ent : cycle->entities)
      {
        //cout << flowPerEnt[ent] << "  ";
        if (flowPerEnt[ent] < 0)
        {
          cycle->flow.set(patch.id, 0.);
          break;
        }
        if (flowPerEnt[ent] < cycle->flow[patch.id])
        {
          cycle->flow.set(patch.id, flowPerEnt[ent]);
        }
        if (ent->concent[patch.id] != 0.)
        {
          float act = 1./(ent->concent[patch.id] * (float) cycle->entities.size()) * flowPerEnt[ent];
          cycle->activity.set( patch.id, cycle->activity[patch.id] + act );
          //cycle->activity[patch.id] += 1./(ent->concent[patch.id] * (float) cycle->entities.size()) * flowPerEnt[ent];
        }
      }
      
      /*
      
       Following contain attempts to define RAC activities based on specificities.
       Not conclusive and mute it for now.
       
      // compute flow of cycle entity associated to 'cycle' + 'other', only counting positive contribution of 'other'
      map<SimEntity *, float> otherPosFlowPerEnt;
      for (auto &ce : cycle->entities)
        otherPosFlowPerEnt[ce] = 0.;

      // compute flow of cycle entity associated 'cycle' + 'other', only counting positive contribution of 'other'
      map<SimEntity *, float> otherNegFlowPerEnt;
      for (auto &ce : cycle->entities)
        otherNegFlowPerEnt[ce] = 0.;
      
      // RAC entity change (absolute value) because of the RAC environment
      map<SimEntity *, float> nonRACFlowPerEnt;
      for (auto &ce : cycle->entities)
        nonRACFlowPerEnt[ce] = 0.;

      for (auto &ce : cycle->entities)
      {
        // if (ce->name == "B2" && curStep==13927) cout << "--- entity --- " << ce->name << " step " << curStep << endl;
        for (auto &r : reactions)
        {
          // does this reaction contains current cycle entity ?
          int stoe = r->stoechiometryOfEntity(ce);
          if (stoe == 0)
            continue;

          if (cycle->containsReaction(r)) // if reaction is in the RAC, count
          {
            otherPosFlowPerEnt[ce] += (float)stoe * r->flow;
            // otherNegFlowPerEnt[ce] += (float) stoe * r->flow;
          }
          else // if reaction is not in the RAC, distinguish positive and negative contributions
          {
            if ((stoe < 0 && r->flow < 0) || (stoe > 0 && r->flow > 0))
              otherPosFlowPerEnt[ce] += (float)stoe * r->flow;
            if ((stoe < 0 && r->flow > 0) || (stoe > 0 && r->flow < 0))
              otherNegFlowPerEnt[ce] += abs((float)stoe * r->flow);
            nonRACFlowPerEnt[ce] += abs((float) stoe * r->flow);
          }
        }
      }
      */
      
      
      // store RAC activity to dynamics history
      if (isCheck || Settings::getInstance()->printHistoryToFile->boolValue() || isMultipleRun || isSpace->boolValue())
      {
        // update history with flowPerEnt
        Array<float> RACentflows;
        //Array<float> RACposSpec;
        //Array<float> RACnegSpec;
        //Array<float> RACspec;
        for (auto &ent : cycle->entities)
        {
          RACentflows.add(flowPerEnt[ent]);
          //RAChistory[currentRun]->getUnchecked(idPAC - 1)->wasRAC = true;
          if (cycle->flow[patch.id] > 0.)
            dynHistory->wasRAC[cycle] = true;
          
          //float specpos = 0.;
          //float specneg = 0.;
          //float spec = 0.;
          // positive specificity
          //if (cycle->flow != 0.) // if cycle is off, +/- specificities are set to 0
          //{
          //  if (otherPosFlowPerEnt[ent] != 0.)
          //    specpos = flowPerEnt[ent] / otherPosFlowPerEnt[ent];
          //  else
          //    specpos = 999.; // there shouldn't be a division by 0 above since otherPosFlowPerEnt at least contains flowPerEnt
                           // never too sure, I use dummy value to spot any unexpected behavior
            // negative specificity
          //  if (flowPerEnt[ent] != 0.)
          //    specneg = (flowPerEnt[ent] - otherNegFlowPerEnt[ent]) / flowPerEnt[ent];
          //  else
          //    specneg = 999.; // there shouldn't be a division by 0 above since condition cycle->flow != 0 prevents flowPerEnt to be 0
            // never too sure, I use dummy value to spot any unexpected behavior
          //}
          //spec = flowPerEnt[ent] / ( abs(flowPerEnt[ent]) + nonRACFlowPerEnt[ent]);
          //RACposSpec.add(specpos);
          //RACnegSpec.add(specneg);
          //RACspec.add(spec);
        }
        // RAChistory[idPAC - 1]->hist.add(new RACSnapshot(cycle->flow, RACentflows));
        //RAChistory[idPAC - 1]->hist.add(new RACSnapshot(cycle->flow, RACentflows, RACposSpec, RACnegSpec, RACspec));
        //RAChistory[currentRun]->getUnchecked(idPAC - 1)->hist.add(new RACSnapshot(cycle->flow, RACentflows, RACposSpec, RACnegSpec, RACspec));
        RACSnapshot snap(cycle->flow[patch.id], RACentflows);
        //snap.step = curStep;
        snap.step = nSteps;
        snap.patchID = patch.id;
        snap.runID = currentRun;
        snap.racID = idPAC-1;
        dynHistory->racHistory.add(snap);
        //if (patch.id == 1)
        //  cout << "in Dyn rac val : " << snap.rac << endl;
        //PACsValuesForDrawing.add(cycle->flow(patch.id));
      }
      
    } // end PAC loop
  } // end space grid loop
  
  
  // if current step is a checkpoint, call new simulation events for drawing
  if (isCheck)
  {
    //Array<float> PACsValues = dynHistory->getLastRACSnapshot().flows;
    Array<float> PACsValues;
    for (auto & cycle : pacList->cycles)
    {
      PACsValues.add(cycle->flow[patchToDraw]);
    }
        
    // update PACs that were on at some point
    Array<bool> RACList;
    for (auto & [cycle, wasrac] : dynHistory->wasRAC)
    {
      RACList.add(wasrac);
    }
    
    //cout << "Step " << curStep << ": adding a RAC array of size : " << PACsValues.size() << endl;
    simNotifier.addMessage(new SimulationEvent(SimulationEvent::NEWSTEP, this, curStep, entityValues, {}, PACsValues, RACList));
  }

  
  
}




void Simulation::updateSinglePatchRates(Patch& patch, bool isCheck)
{
  
  // calculate new reaction rates
  SteppingReactionRates(patch, isCheck);
  
  // calculate creation/destruction rates
  SteppingInflowOutflowRates(patch);

  // calculate diffusion rates w.r.t closest patch neighbours
  SteppingDiffusionRates(patch);
  
  
}


void Simulation::SteppingReactionRates(Patch& patch, bool isCheck)
{
    
  // loop through reactions
  for (auto &reac : reactions)
  {
    // for a sanity check
    //cout << "##### " << reac->name << " :" << endl;
    //cout << "\tassoc/dissoc k : " << reac->assocRate << " ; " << reac->dissocRate << endl;
    if (!reac->enabled)
      continue;
    
    // multiply reactants/products concentration together
    float minReacConcent = 100.;
    float mindReacConcent = 100.;
    float minProdConcent = 100.;
    float mindProdConcent = 100.;
    float reacConcent = 1.;
    float deterministicReacConcent = 1.;
    bool firstEnt = true;
    for (auto &ent : reac->reactants)
    {
      reacConcent *= ent->concent[patch.id];
      deterministicReacConcent *= ent->deterministicConcent[patch.id];
      //cout << "localReac::" << ent->name << ": " << ent->concent << "  :  " << ent->deterministicConcent << endl;
      if (ent == reac->reactants[0] || ent->concent[patch.id] < minReacConcent)
        minReacConcent = ent->concent[patch.id];
      if (ent == reac->reactants[0] || ent->deterministicConcent[patch.id] < mindReacConcent)
        mindReacConcent = ent->deterministicConcent[patch.id];
    }
    float prodConcent = 1.;
    float deterministicProdConcent = 1.;
    firstEnt = true;
    for (auto &ent : reac->products)
    {
      prodConcent *= ent->concent[patch.id];
      deterministicProdConcent *= ent->deterministicConcent[patch.id];
      if (ent == reac->products[0] || ent->concent[patch.id] < minProdConcent)
        minProdConcent = ent->concent[patch.id];
      if (ent == reac->products[0] || ent->deterministicConcent[patch.id] < mindProdConcent)
        mindProdConcent = ent->deterministicConcent[patch.id];
    }


    // multiply concentrations by froward/backward constant rates
    float directCoef = reacConcent * reac->assocRate;
    float deterministicDirectCoef = deterministicReacConcent * reac->assocRate;
    float reverseCoef = prodConcent * reac->dissocRate;
    float deterministicReverseCoef = deterministicProdConcent * reac->dissocRate;
    if (!reac->isReversible)
    {
      reverseCoef = 0.;
      deterministicReverseCoef = 0.;
    }
    
    // init increments
    float directIncr = directCoef * dt->floatValue();
    float deterministicDirectIncr = deterministicDirectCoef * dt->floatValue();
    float reverseIncr = reverseCoef * dt->floatValue();
    float deterministicReverseIncr = deterministicReverseCoef * dt->floatValue();

    //if (print)
    //{
     // cout << "K+ = " << reac->assocRate << endl;
     // for (auto & ent : reac->reactants)
     // {
     //   cout << "[" << ent->name << "] = " << ent->concent << endl;
     // }
      //cout << "forward incr = " << directIncr << " det. forward incr = " << deterministicDirectIncr  << endl;
    //}

    // adjust the increments depending on available entities
    directIncr = jmin(directIncr, minReacConcent);
    deterministicDirectIncr = jmin(deterministicDirectIncr, mindReacConcent);
    reverseIncr = jmin(reverseIncr, minProdConcent);
    deterministicReverseIncr = jmin(deterministicReverseIncr, mindProdConcent);

    // to treat reactions equally: save increments for later. increase() and decrease() store changes to make, and refresh() will effectively make them

    // increase and decrease entities
    for (auto &ent : reac->reactants)
    {
      ent->increase(patch.id, reverseIncr);
      ent->deterministicIncrease(patch.id, deterministicReverseIncr);
      ent->decrease(patch.id, directIncr);
      ent->deterministicDecrease(patch.id, deterministicDirectIncr);
    }
    for (auto &ent : reac->products)
    {
      ent->increase(patch.id, directIncr);
      ent->deterministicIncrease(patch.id, deterministicDirectIncr);
      ent->decrease(patch.id, reverseIncr);
      ent->deterministicDecrease(patch.id, deterministicReverseIncr);
    }
    
    
    // demographic noise
    if (stochasticity->boolValue())
    {
      float stoc_directIncr = sqrt(reac->assocRate) * noiseEpsilon;
      float stoc_reverseIncr = sqrt(reac->dissocRate) * noiseEpsilon;
      // for a sanity check
      //string testname = "2+2=4";
      //bool print(testname==reac->name ? true : false);
      
      // forward reaction
      map<SimEntity*, double> m;
      for (auto& ent : reac->reactants)
      {
        if (!m.count(ent)) // if entity has not been parsed already
        {
          stoc_directIncr *= sqrt(ent->concent[patch.id]);
          m[ent] = 1;
        }
        else
        {
          float corrC = ent->concent[patch.id] - noiseEpsilon * noiseEpsilon * m[ent];
          if (corrC > 0.) stoc_directIncr *= sqrt(corrC);
          else stoc_directIncr = 0.;
          m[ent]++;
        }
      }
      
      // random fluctuation of forward reaction associated to current timestep
      float sqrtdt = sqrt(dt->floatValue());
      float directWiener = rgg->randomNumber()*sqrtdt; // gaus random in N(0, 1) x sqrt(dt)
      //if (print) cout << "forward wiener : " << directWiener << endl;
      stoc_directIncr *= directWiener;
      
      
      // backward reaction
      if (!reac->isReversible)
        stoc_reverseIncr = 0.;
      else
      {
        map<SimEntity*, double> mm;
        for (auto& ent : reac->products)
        {
          if (!mm.count(ent)) // if entity has not been parsed already
          {
            stoc_reverseIncr *= sqrt(ent->concent[patch.id]);
            mm[ent] = 1;
          }
          else
          {
            float corrC = ent->concent[patch.id] - noiseEpsilon * noiseEpsilon * mm[ent];
            if (corrC > 0.) stoc_reverseIncr *= sqrt(corrC);
            else stoc_reverseIncr = 0.;
            mm[ent]++;
          }
        }
      }
      
      // random fluctuation of forward reactions associated to current timestep
      float reverseWiener = rgg->randomNumber()*sqrtdt;
      //if (print) cout << "backward wiener : " << reverseWiener << endl;
      stoc_reverseIncr *= reverseWiener;
      
      // increase and decrease entities
      for (auto &ent : reac->reactants)
      {
        ent->increase(patch.id, stoc_reverseIncr);
        ent->decrease(patch.id, stoc_directIncr);
      }
      for (auto &ent : reac->products)
      {
        ent->increase(patch.id, stoc_directIncr);
        ent->decrease(patch.id, stoc_reverseIncr);
      }

      
    } // end if stochasticity

          
    // update flow needed only at checkpoints
    if (isCheck || isMultipleRun)
    {
      //reac->flow = directCoef - reverseCoef;
      //reac->deterministicFlow = deterministicDirectCoef - deterministicReverseCoef;
      reac->flow.set(patch.id, directCoef - reverseCoef);
      reac->deterministicFlow.set(patch.id, deterministicDirectCoef - deterministicReverseCoef);
    }
  } // end reaction loop
  
  
}


void Simulation::SteppingInflowOutflowRates(Patch& patch)
{
  
  // loop over entities
  for (auto &ent : entities)
  {
    ent->previousConcent.set(patch.id, ent->concent[patch.id]); // save concent in previousConcent to compute var speed
    
    // creation
    if (ent->primary)
    {
      float incr = ent->creationRate * dt->floatValue();
      float deterministicIncr = ent->creationRate * dt->floatValue();
      
      // demographic noise
      if (stochasticity->boolValue())
      {
        float stocIncr = sqrt(ent->creationRate) * noiseEpsilon;
        float wiener = rgg->randomNumber() * sqrt(dt->floatValue());
        stocIncr *= wiener;
        incr -= stocIncr;
      } // end if stochasticity
      
      ent->increase(patch.id, incr);
      ent->deterministicIncrease(patch.id, deterministicIncr);
    }
    
    //destruction
    float rate = ent->concent[patch.id] * ent->destructionRate;
    float incr = rate * dt->floatValue();
    float deterministicRate = ent->deterministicConcent[patch.id] * ent->destructionRate;
    float deterministicIncr = deterministicRate * dt->floatValue();


    // demographic noise
    if (stochasticity->boolValue())
    {
      double stocIncr = sqrt(rate) * noiseEpsilon;
      float wiener = rgg->randomNumber() * sqrt(dt->floatValue());
      stocIncr *= wiener;
      incr -= stocIncr;
    } // end if stochasticity
    
    ent->decrease(patch.id, incr);
    ent->deterministicDecrease(patch.id, deterministicIncr);
    
    //if (curStep<=10) cout << "Destruction increment:: " << curStep << " -> " << deterministicIncr << "  :  " << incr << endl;

  } // end loop over entities

  

  
}


void Simulation::SteppingDiffusionRates(Patch& patch)
{
  
  // loop over neighbour patches of current patch
  for (auto& neighbour : patch.neighbours)
  {
    // loop over entities
    for (auto& ent : entities)
    {
      float grad = ent->concent[patch.id] - ent->concent[neighbour];
      float detgrad = ent->deterministicConcent[patch.id] - ent->deterministicConcent[neighbour];
      
      float incr = -grad * Space::getInstance()->diffConstant->floatValue();
      float detIncr = -detgrad * Space::getInstance()->diffConstant->floatValue();
      // atually it is -grad * kd / L where L is the distance between two patches. Included in kd definition
      
      if (stochasticity->boolValue())
      {
        // *** TODO
      }
      
      // increase concentrations of entities
      ent->increase(patch.id, incr);
      ent->deterministicIncrease(patch.id, incr);
    }
  }
  
}



void Simulation::stop()
{
  finished->setValue(true);

  if (getUserListMode())
  {
    updateUserListFromSim(0);
  }
  state = Idle;
  isMultipleRun = false;
  //redrawRun = false;

  // if (!express)
  //{
  //	loadToManualMode();
  //
}

void Simulation::cancel()
{
  if (isComputing)
    shouldStop = true; // to stop PAC/CAC computation
  stopThread(500);
}



void Simulation::run()
{
  curStep = 0;
  nSteps = 0;
  if (!express)
    LOG("--------- Start thread ---------");
  finished->setValue(false);
  if (redrawRun || redrawPatch)
  {
    // recover dynamics of concentrations and RAC corresponding to run or patch to redraw
    Array<ConcentrationSnapshot> concDyn = dynHistory->getConcentrationDynamicsForRunAndPatch(runToDraw, patchToDraw);
    Array<RACSnapshot> racDyn = dynHistory->getRACDynamicsForRunAndPatch(runToDraw, patchToDraw);
    
    cout << "Retrieved " <<  concDyn.size() << " conc snapshots and " << racDyn.size() << " rac snapshots" << endl;
    
    
    /*
    if (concDyn.size() != racDyn.size())
    {
      LOG("concentration dynamics and rac dynamics differ in size, cannot redraw run " + String(to_string(currentRun)));
      return;
    }
    */
    
    //cout << "--- ORDERED CHECK ---" << endl;
    //for (auto & rs : racDyn)
    //  cout << rs.step << endl;

    int k=0;
    int flag = 0;
    while (!finished->boolValue() && !threadShouldExit())
    {
      if (k<maxSteps)
      {
        // retrieve all racs values for this step
        Array<RACSnapshot> thisStepRACs;
        for (int k2=flag; k2<racDyn.size(); k2++)
        {
          if (racDyn.getUnchecked(k2).step == curStep)
          {
            thisStepRACs.add(racDyn.getUnchecked(k2));
          }
          else
          {
            flag = k2;
            break;
          }
        }
        /*
        cout << "--- SANITY CHECK ---" << endl;
        int count=0;
        for (int k2=flag; k2<racDyn.size(); k2++)
        {
          if (racDyn.getUnchecked(k2).step == curStep)
            count++;
        }
        cout << "found " << count << " matching rac snaps at step " << curStep << ". thisSTepRacsize : " << thisStepRACs.size() << endl;
        cout << "--- ------ ------ ---" << endl;
        */
        
        //nextRedrawStep(concDyn.getUnchecked(k), racDyn.getUnchecked(k));
        nextRedrawStep(concDyn.getUnchecked(k), thisStepRACs);
        k++;
      }
      else
        finished->setValue(true);
    }
  }
  else
  {
    while (!finished->boolValue() && !threadShouldExit())
    {
      nextStep();
    }
  }
  
  
  if (!express)
    LOG("--------- End thread ---------");

  Array<float> entityValues;
  for (auto &ent : entities)
  {
    if (!redrawRun)
      entityValues.add(ent->concent[0]);
    else
    {
      int lastrunstep = maxSteps+maxSteps*setRun->intValue()-1;
      entityValues.add(ent->concentHistory[lastrunstep].second);
    }
  }

  simNotifier.addMessage(new SimulationEvent(SimulationEvent::FINISHED, this, curStep, entityValues, {}, {}, {}));
  
  if (redrawRun || redrawPatch)
  {
    redrawRun = false;
    redrawPatch = false;
    return;
  }
  if (express)
  {
    // writeJSONConcents();
    return;
  }

  // I muted the following, I can be adapted to Array<Float> with things like :
  // cout << std::max_element(recordConcent.begin(), recordConcent.end());
  /*
  LOG("Record Concentration: " << recordConcent << " for entity " << recordEntity);
  if (recordDrawn < recordConcent)
    LOG("Record Drawn Concentration: " << recordDrawn << " for entity " << recordDrawnEntity);
  */
  LOG("Max RAC: " << pacList->maxRAC);
  LOG("RACS:");

  pacList->printRACs();

  updateConcentLists();

  if (Settings::getInstance()->printHistoryToFile->boolValue())
  {
    //LOG("Printing history to file not enabled for now, disabling it in Settings");
    //Settings::getInstance()->printHistoryToFile->setValue(false);
    writeHistory();
  }

  // listeners.call(&SimulationListener::simulationFinished, this);
  startTrigger->setEnabled(true);
}

///////////////////////////////////////////////////////////////////:

void Simulation::writeHistory()
{
 // int nruns = RAChistory.size();
 // if (nruns==0)
 //   return;
  
  
  
  if (dynHistory->concentHistory.size() != dynHistory->racHistory.size())
  {
    LOGWARNING("RAC history and concentration history array have different size, will not print them to file.");
    cout << "concent history size : " << dynHistory->concentHistory.size() << " VS RAC history size : " << dynHistory->racHistory.size() << endl;
    return;
  }
  
  // output file
  String filename = "dynamicsHistory.csv";
  ofstream historyFile;
  historyFile.open(filename.toStdString(), ofstream::out | ofstream::trunc);
  
  // first line
  historyFile << "Run,Patch,Step,";
  int c=-1;
  for (auto & ent : entities)
  {
    c++;
    string comma = ",";
    if ( c == (entities.size() - 1) && pacList->cycles.size()==0)
      comma = "";
    historyFile << "[" << ent->name << "]" << comma;
  }
  c=-1;
  for (auto & cycle : pacList->cycles)
  {
    c++;
    string comma = (c == (pacList->cycles.size() - 1)) ? "" : ",";
    historyFile << "RAC_" << c  << comma;
  }
  historyFile << endl;
  
  // print dynamics to file
  for (int k=0; k<dynHistory->concentHistory.size(); k++)
  {
    
    if (dynHistory->concentHistory.getUnchecked(k).runID != dynHistory->racHistory.getUnchecked(k).runID)
    {
      LOGWARNING("Run id Conflict when printing to file, stop.");
      historyFile.flush();
      return;
    }
    
    if (dynHistory->concentHistory.getUnchecked(k).patchID != dynHistory->racHistory.getUnchecked(k).patchID)
    {
      LOGWARNING("Patch id Conflict when printing to file, stop.");
      historyFile.flush();
      return;
    }
    
    if (dynHistory->concentHistory.getUnchecked(k).step != dynHistory->racHistory.getUnchecked(k).step)
    {
      LOGWARNING("Step id Conflict when printing to file, stop.");
      //cout << dynHistory->concentHistory.getUnchecked(k).step << " " << dynHistory->racHistory.getUnchecked(k).step << endl;
      historyFile.flush();
      return;
    }
    
    historyFile << dynHistory->concentHistory.getUnchecked(k).runID << ",";
    historyFile << dynHistory->concentHistory.getUnchecked(k).patchID << ",";
    historyFile << dynHistory->concentHistory.getUnchecked(k).step << ",";
    
    // print concentration snapshots
    c=-1;
    for (auto &ent : entities)
    {
      c++;
      string comma = ",";
      if ( c == (entities.size() - 1) && pacList->cycles.size()==0)
        comma = "";
      historyFile << dynHistory->concentHistory.getUnchecked(k).conc[ent] << comma;
    }
    
    // print rac snapshots
    c=-1;
    //for (auto & cycle : pacList->cycles)
    for (int kc=0; kc<pacList->cycles.size(); kc++)
    {
      c++;
      string comma = (c == (pacList->cycles.size() - 1)) ? "" : ",";
      historyFile << dynHistory->racHistory.getUnchecked(k).flows[kc] << comma;
    }
  historyFile << endl;
  }
  
    
    
    /*
    // loop over runs
    for (int irun=0; irun<nruns; irun++)
    {
      //Array<RACHist> runRACHistory = RAChistory[irun];
      
      // test if no history
      if (RAChistory[irun]->getUnchecked(idPAC0)->hist.size() == 0)
      {
        LOG("RAC " + String(idPAC) + " history empty");
        historyFile.close();
        continue;
      }
      
      
      int i = 0;
      for (auto &snap : RAChistory[irun]->getUnchecked(idPAC0)->hist)
      {
        i++;
        if (i == 1)
          historyFile << RAChistory[irun]->getUnchecked(idPAC0)->pacScore << ",";
        else
          historyFile << ",";
        historyFile << irun << "," << i << "," << snap->rac << ",";
        for (int e = 0; e < snap->flows.size(); e++)
        {
          historyFile << snap->flows[e] << ",";
          historyFile << snap->posSpecificities[e] << ",";
          historyFile << snap->negSpecificities[e] << ",";
          historyFile << snap->specificity[e];
        }
        historyFile << endl;
      } // end snap loop
    } // end run loop
  historyFile.close();
  }
  LOG("RAC History written to files RACi.csv");

  
  // store concentration of all entity concentrations history to csv file
  String concentFilename = "./concentrationDynamics.csv";
  ofstream outfile;
  outfile.open(concentFilename.toStdString(), ofstream::out | ofstream::trunc);

  // 1st line of the file is column name : time and entities
    outfile << "time,runID,";
    for (int ient = 0; ient < entities.size(); ient++)
    {
      string comma = (ient == (entities.size() - 1)) ? "" : ",";
      outfile << "[" << entities[ient]->name << "]" << comma;
    }
    outfile << endl;

  // now store concentration history
  int npoints = entities[0]->concentHistory.size();
  //for (int s = 0; s < (nSteps - 1)*nRuns; s++)
  for (int s = 0; s < npoints; s++)
  {
    float thisrun = (float) entities[0]->concentHistory[s].first;
    float fs = (float)s;
    float time = (fs - thisrun * (float) maxSteps) * dt->floatValue();
    //outfile << time << "," << kRun << ",";
    outfile << time << "," << entities[0]->concentHistory[s].first << ",";
    int c = 0;
    for (auto &ent : entities)
    {
      string comma = (c == (entities.size() - 1)) ? "" : ",";
      //outfile << ent->concentHistory[s] << comma;
      outfile << ent->concentHistory[s].second << comma;
      c++;
    }
    outfile << endl;
  }
  
  
  
  // close concentration file output
  outfile.close();
  */
  
}

///////////////////////////////////////////////////////////////////:

void Simulation::PrintSimuToFile(string filename = "model.txt")
{
  ofstream output;
  output.open(filename, ofstream::out | ofstream::trunc);

  output << "--------------------------" << endl;
  output << "---- Simulation Content ----" << endl;
  output << "--------------------------\n"
         << endl;
  output << "--- Some global parameters" << endl;
  output << "Nprimaries: " << Generation::getInstance()->primEntities->stringValue() << endl;
  output << "path to z3: " << Settings::getInstance()->pathToz3->stringValue() << endl;
  output << "z3 timeout: " << Settings::getInstance()->z3timeout->floatValue() / 1000. << "s" << endl;
  output << "maxlevel: " << Generation::getInstance()->numLevels->stringValue() << endl;
  output << "reaction proportion: " << Generation::getInstance()->propReactions->stringValue() << endl;
  output << endl;

  output << "--- Entities [name; composition; free energy]" << endl;
  for (auto &e : entities)
  {
    output << "[ " << e->name << " ; (";
    for (auto &i : e->composition)
      output << i;
    output << ") ; " << e->freeEnergy << " ]" << endl;
  }
  output << endl;

  output << "--- Reactions 'reactants --> products' [k+ ; k-]" << endl;
  for (auto &r : reactions)
  {
    output << "'";
    int nreac = r->reactants.size();
    int c = 0;
    for (auto &reac : r->reactants)
    {
      output << reac->name;
      if (c < (nreac - 1))
        output << " + ";
      c++;
    }
    output << " --> ";
    int nprod = r->products.size();
    c = 0;
    for (auto &prod : r->products)
    {
      output << prod->name;
      if (c < (nprod - 1))
        output << " + ";
      c++;
    }
    output << " \t[" << r->assocRate << " ; " << r->dissocRate << "]" << endl;
  }
}

///////////////////////////////////////////////////////////////////:

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
    for (int k=0; k<Space::getInstance()->nPatch; k++)
    {
      var v = new DynamicObject();
      v.getDynamicObject()->setProperty("patch", k);
      v.getDynamicObject()->setProperty("Start", e->startConcent[k]);
      v.getDynamicObject()->setProperty("End", e->concent[k]);
      ent.append(v);
    }
    data.getDynamicObject()->setProperty(e->name, ent);
  }
  return data;
}

SimEntity *Simulation::getSimEntityForName(const String &nameToFind)
{
  for (auto &se : entities)
  {
    if (se->name == nameToFind)
      return se;
  }
  LOGWARNING("Failed to find SimEntity for name " << nameToFind);
  return nullptr;
}

SimEntity *Simulation::getSimEntityForID(const size_t idToFind)
{
  for (auto &se : entities)
  {
    if (se->idSAT == idToFind)
      return se;
  }
  LOGWARNING("Failed to find SimEntity for id " << idToFind);
  return nullptr;
}

SimReaction *Simulation::getSimReactionForName(const String &nameToFind)
{
  for (auto &sr : reactions)
  {
    if (sr->name == nameToFind)
      return sr;
  }
  LOGWARNING("Failed to find SimReaction for name " << nameToFind);
  return nullptr;
}

void Simulation::updateConcentLists()
{
  if (express)
    return;

  // TO update with refactor
  // for (auto& ent : EntityManager::getInstance()->items)
  //{
  //	auto se = ent->simEnt;
  //	if (se != nullptr)
  //	{
  //		ent->concent->setValue(se->concent);
  //	}
  //	else
  //	{
  //		LOGWARNING("No SimEntity for entity " << ent->niceName);
  //	}
  // }
}

void Simulation::onContainerTriggerTriggered(Trigger *t)
{
  express = Generation::getInstance()->statistics->boolValue();
  if (t == genTrigger)
  {
    fetchGenerate();
  }
  else if (t == genstartTrigger)
  {
    if (express)
    {
      LOG("Compute stats");
      Statistics::getInstance()->computeStats();
    }
    else
    {
      fetchGenerate();
      start(true);
    }
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

void Simulation::setConcToCAC(int idCAC)
{
  if (idCAC < 1)
    return;
  CACType cac = pacList->CACfromInt(idCAC);
  for (auto entConc : cac.second)
  {
    auto ent = entConc.first;
    float conc = entConc.second;
    ent->concent = conc;
    if (ent->entity != nullptr)
      ent->entity->concent->setValue(conc);
    else
      LOGWARNING("SetCAC: No entity for SimEntity"+ent->name);
  }
}

void Simulation::setConcToSteadyState(int idSS)
{
  if (idSS < 1)
    return;
  SteadyState ss = steadyStatesList->arraySteadyStates[idSS - 1];
  int ident = 0;
  for (auto ent : entities)
  {
    float conc = ss.state[ident].second;
    ent->concent = conc;
    ident++;
    if (ent->entity != nullptr)
      ent->entity->concent->setValue(conc);
  }
}


void Simulation::drawConcOfRun(int idrun)
{
  /*
  cout << "--- sanity check ---" << endl;
  cout << "Will draw run#" << idrun << endl;
  cout << "Should have " << round(totalTime->floatValue() / dt->floatValue()) << " steps" << endl;
  cout << "Number of runs in RAChistory : " << RAChistory.size() << endl;
  cout << "Number of PACs/steps in each RAChistory : " << RAChistory.size() << endl;
  for (int irun=0; irun<RAChistory.size(); irun++)
  {
    cout << "run #" << irun << " has " << RAChistory[irun]->size() << " RAC(s)" << endl;
    for (int ipac=0; ipac<RAChistory[irun]->size(); ipac++)
    {
      cout << "\tRAC #" << ipac << " has " << RAChistory[irun]->getUnchecked(ipac)->hist.size() << " steps recorded" << endl;
      for (int ir=0; ir<RAChistory[irun]->getUnchecked(ipac)->hist.size(); ir++)
        cout << RAChistory[irun]->getUnchecked(ipac)->hist[ir]->rac << "  ";
      cout << endl;
    }
  }
  */
  // check if some simulation exists before redrawing
  bool isOK = true;
  for (auto & ent : entities)
  {
    if (ent->concentHistory.size()==0)
    {
      isOK = false;
      break;
    }
  }
  if (!isOK)
  {
    LOG("You must start some simulation before choosing which run to draw");
    return;
  }
  
  // check if number of runs chosen in setRuns and number of runs stored in current simul match
  if (setRun->intValue() >= RAChistory.size())
  {
    LOG("Index of chosen run to draw exceeds numbers of runs currently stored in simul. Can't draw run #" + to_string(setRun->intValue()));
    return;
  }
/*
  // checks if number of checkpoints changed since last start, otherwise that would mess with RAC display
  if (checkPoint != maxSteps/pointsDrawn->intValue())
  {
    cout << "current checkpoint value = " << pointsDrawn->intValue() << endl;
    cout << "previous checkpoint value = maxSteps / checkpoint = " << maxSteps << " / " << checkPoint << " = " << maxSteps/checkPoint << endl;
    LOG("Checkpoint parameter changed since last simulation. Please run simulation again.");
    return;
  }
  */
  // update checkpoint if user changed it since last simu
  checkPoint = maxSteps / pointsDrawn->intValue();
  checkPoint = jmax(1, checkPoint);
  
  stopThread(100);
  redrawRun = true;
  runToDraw = setRun->intValue();
  patchToDraw = 0;
  for (int k=0; k<recordDrawn.size(); k++)
    recordDrawn.set(k, 0);
  currentRun = setRun->intValue();
  simNotifier.addMessage(new SimulationEvent(SimulationEvent::WILL_START, this));
  startThread();
  
}


void Simulation::drawConcOfPatch(int idpatch)
{
  

/*
  // checks if number of checkpoints changed since last start, otherwise that would mess with RAC display
  if (checkPoint != maxSteps/pointsDrawn->intValue())
  {
    cout << "current checkpoint value = " << pointsDrawn->intValue() << endl;
    cout << "previous checkpoint value = maxSteps / checkpoint = " << maxSteps << " / " << checkPoint << " = " << maxSteps/checkPoint << endl;
    LOG("Checkpoint parameter changed since last simulation. Please run simulation again.");
    return;
  }
*/
  
  stopThread(100);
  redrawPatch = true;
  runToDraw = 0;
  patchToDraw = idpatch;
  
  // update checkpoint if user changed it since last simu
  checkPoint = maxSteps / pointsDrawn->intValue();
  checkPoint = jmax(1, checkPoint);
  
  for (int k=0; k<recordDrawn.size(); k++)
    recordDrawn.set(k, 0);
  currentRun = setRun->intValue();
  simNotifier.addMessage(new SimulationEvent(SimulationEvent::WILL_START, this));
  startThread();
  
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
  if (p == setCAC)
  {
    if (setCAC->intValue() < 1)
      return;
    setConcToCAC(setCAC->intValue());
  }
  if (p == setSteadyState)
  {
    if (setSteadyState->intValue() < 1)
      return;
    setConcToSteadyState(setSteadyState->intValue());
  }
  if (p == setRun)
  {
    if (setRun->intValue() < 0)
      return;
    if (state!=Simulating && !Engine::mainEngine->isLoadingFile) 
      drawConcOfRun(setRun->intValue());
  }
  if (p == isSpace)
  {
    if (!isSpace->boolValue())
      Space::getInstance()->tilingSize->setValue(1);
  }

  /*if (liveUpdate->boolValue())
  {
    if (p == totalTime || p == pointsDrawn)
    {
      start();
    }
  }
  */
}


