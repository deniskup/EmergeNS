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
  epsilonEq = addFloatParameter("Eps.", "Epsilon for equilibrium detection", 0.001f, 0.f, 1.f);
  // ready = addBoolParameter("Ready","Can the simulation be launched ?", false);
  setCAC = addEnumParameter("Set CAC", "Set current concentrations according to CAC witness");
  setSteadyState = addEnumParameter("Set Steady State", "Set current concentrations to steady state");
  ignoreFreeEnergy = addBoolParameter("Ignore Free Energy", "Ignore free energy of entities in the simulation", false);
  ignoreBarriers = addBoolParameter("Ignore Barriers", "Ignore barrier energy of reactions in the simulation", false);
  stochasticity = addBoolParameter("Stochasticity", "Add stochasticity in the simulation dynamics", false);

  
  dt->setAttributeInternal("stringDecimals", DT_PRECISION);
  maxSteps = (int)(totalTime->floatValue() / dt->floatValue());
  maxSteps = jmax(1, maxSteps);
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
  //}
  // update the parameters of the simulation in the UI
  simNotifier.addMessage(new SimulationEvent(SimulationEvent::UPDATEPARAMS, this));
}

// to save additional data, different from getJSONdata()
var Simulation::toJSONData()
{
  var data = new DynamicObject();
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
  return data;
}

void Simulation::importJSONData(var data)
{
  clearParams();
  if (data.isVoid())
    return;
  if (data.getDynamicObject() == nullptr)
    return;

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

  // precision
  dt->setAttributeInternal("stringDecimals", DT_PRECISION);
  Settings::getInstance()->CACRobustness->setAttributeInternal("stringDecimals", CACROB_PRECISION);
  computeBarriers();
  updateParams();
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

void Simulation::updateUserListFromSim()
{
  // clear previous  (beware of the order !)

  // filter array to retrieve only disabled ones

  // load entities
  for (auto &se : entities)
  {
    if (Entity *e = EntityManager::getInstance()->getItemWithName(se->name, true))
    {
      e->simEnt = se;
      e->concent->setValue(se->concent);
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
      newItems.add(new Entity(e));
    UndoMaster::getInstance()->performAction("Generate new entity list", EntityManager::getInstance()->getAddItemsUndoableAction(newItems));

    // same for reactions
    Array<Reaction *> newReactions;
    for (auto &r : reactions)
      newReactions.add(new Reaction(r));
    UndoMaster::getInstance()->performAction("Generate new reaction list", ReactionManager::getInstance()->getAddItemsUndoableAction(newReactions));
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

void Simulation::start(bool restart)
{

  stopThread(100);

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

  state = Simulating;

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

  startTrigger->setEnabled(false);
  if (!express)
    simNotifier.addMessage(new SimulationEvent(SimulationEvent::WILL_START, this));
  // listeners.call(&SimulationListener::simulationWillStart, this);

  Array<float> entityValues;
  Array<Colour> entityColors;

  for (auto &ent : entitiesDrawn)
  {
    entityValues.add(ent->concent);
    entityColors.add(ent->color);
  }

  if (!express)
    simNotifier.addMessage(new SimulationEvent(SimulationEvent::STARTED, this, 0, entityValues, entityColors));
  // listeners.call(&SimulationListener::simulationStarted, this);
  recordConcent = 0.;
  recordDrawn = 0.;

  // remove RACs
  for (auto &pac : pacList->cycles)
  {
    pac->wasRAC = false;
  }
  pacList->maxRAC = 0.;
  
  // clear concentration histories of entities
  for (auto& ent: entities)
  {
    ent->concentHistory.clear();
  }

  RAChistory.clear();
  for (auto &pac : pacList->cycles)
  {
    // RAChistory.add(new RACHist());
    // RAChistory.add(new RACHist(pac->entities));
    RAChistory.add(new RACHist(pac->entities, pac->score));
  }
  checkPoint = maxSteps / pointsDrawn->intValue(); // draw once every "chekpoints" steps
  checkPoint = jmax(1, checkPoint);
  if (stochasticity->boolValue())
  {
    rgg = new RandomGausGenerator(0., 1.); // init random generator
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
  
  startThread();
}

void Simulation::nextStep()
{

  nSteps++;

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

  // loop through reactions (first to see brief RACs)
  for (auto &reac : reactions)
  {
    // for a sanity check
    //string testname = "2+2=4";
    //bool print(testname==reac->name ? true : false);
    
    if (!reac->enabled)
      continue;
    // shorter names
    float minReacConcent = 100.;
    float mindReacConcent = 100.;
    float minProdConcent = 100.;
    float mindProdConcent = 100.;
    float reacConcent = 1.;
    float deterministicReacConcent = 1.;
    for (auto &ent : reac->reactants)
    {
      reacConcent *= ent->concent;
      deterministicReacConcent *= ent->deterministicConcent;
///      cout << "localReac::" << ent->name << ": " << ent->concent << "  :  " << ent->deterministicConcent << endl;
      if (ent == reac->reactants[0] || ent->concent < minReacConcent)
        minReacConcent = ent->concent;
      if (ent == reac->reactants[0] || ent->deterministicConcent < mindReacConcent)
        mindReacConcent = ent->deterministicConcent;
    }
    float prodConcent = 1.;
    float deterministicProdConcent = 1.;
    for (auto &ent : reac->products)
    {
      prodConcent *= ent->concent;
      deterministicProdConcent *= ent->deterministicConcent;
      if (ent == reac->products[0] || ent->concent < minProdConcent)
        minProdConcent = ent->concent;
      if (ent == reac->products[0] || ent->deterministicConcent < mindProdConcent)
        mindProdConcent = ent->deterministicConcent;
    }

    // float reac1Concent = reac->reactant1->concent;
    // float reac2Concent = reac->reactant2->concent;
    // float prodConcent = reac->product->concent;
    //  compute product of reactants concentrations
    // float reacConcent = reac1Concent * reac2Concent;

    float directCoef = reacConcent * reac->assocRate;
    float deterministicDirectCoef = deterministicReacConcent * reac->assocRate;
    float reverseCoef = prodConcent * reac->dissocRate;
    float deterministicReverseCoef = deterministicProdConcent * reac->dissocRate;
    if (!reac->isReversible)
    {
      reverseCoef = 0.;
      deterministicReverseCoef = 0.;
    }
///    cout << "globalreacCoef check: " << directCoef << "  :  " << deterministicDirectCoef << endl;
    
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
     // cout << "deterministic forward incr = " << directIncr << endl;
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
      ent->increase(reverseIncr);
      ent->deterministicIncrease(deterministicReverseIncr);
      ent->decrease(directIncr);
      ent->deterministicDecrease(deterministicDirectIncr);
    }
    for (auto &ent : reac->products)
    {
      ent->increase(directIncr);
      ent->deterministicIncrease(deterministicDirectIncr);
      ent->decrease(reverseIncr);
      ent->deterministicDecrease(deterministicReverseIncr);
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
          stoc_directIncr *= sqrt(ent->concent);
          m[ent] = 1;
        }
        else
        {
          float corrC = ent->concent - noiseEpsilon * noiseEpsilon * m[ent];
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
      if (!reac->isReversible) stoc_reverseIncr = 0.;
      else
      {
        map<SimEntity*, double> mm;
        for (auto& ent : reac->products)
        {
          if (!mm.count(ent)) // if entity has not been parsed already
          {
            stoc_reverseIncr *= sqrt(ent->concent);
            mm[ent] = 1;
          }
          else
          {
            float corrC = ent->concent - noiseEpsilon * noiseEpsilon * mm[ent];
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
        ent->increase(stoc_reverseIncr);
        ent->decrease(stoc_directIncr);
      }
      for (auto &ent : reac->products)
      {
        ent->increase(stoc_directIncr);
        ent->decrease(stoc_reverseIncr);
      }

      
    } // end if stochasticity

    //if (curStep<=10) cout << "forward reaction flow:: " << curStep << " -> " << deterministicIncr << "  :  " << incr << endl;
    
    // update flow needed only at checkpoints
    if (isCheck)
    {
      reac->flow = directCoef - reverseCoef;
      reac->deterministicFlow = deterministicDirectCoef - deterministicReverseCoef;
      //cout << "check : " << directCoef << "  :  " << reverseCoef << endl;
      //cout << curStep <<  " -> " << reac->flow << "  ;  " << reac->deterministicFlow << endl;
    }
  }

  // creation/destruction
  for (auto &ent : entities)
  {
    ent->previousConcent = ent->concent; // save concent in previousConcent to compute var speed
    
    // creation
    if (ent->primary)
    {
      ent->increase(ent->creationRate * dt->floatValue());
      ent->deterministicIncrease(ent->creationRate * dt->floatValue());
    }
    
    //destruction
    float rate = ent->concent * ent->destructionRate;
    float deterministicRate = ent->deterministicConcent * ent->destructionRate;
    // decrease rate = - kd * [entity] * dt + noise
    float deterministicIncr = deterministicRate * dt->floatValue();
    float incr = rate * dt->floatValue();

    // demographic noise
    if (stochasticity->boolValue())
    {
      double stocIncr = sqrt(rate) * noiseEpsilon;
      float wiener = rgg->randomNumber() * sqrt(dt->floatValue());
      stocIncr *= wiener;
      incr -= stocIncr;
    } // end if stochasticity
    
    ent->decrease(incr);
    ent->deterministicDecrease(deterministicIncr);
    
    //if (curStep<=10) cout << "Destruction increment:: " << curStep << " -> " << deterministicIncr << "  :  " << incr << endl;

  } // end loop over entities

  curStep++;
  perCent->setValue((int)((curStep * 100) / maxSteps));

  float maxVar = 0.;

  for (auto &ent : entities)
  {

    if (Settings::getInstance()->printHistoryToFile->boolValue())
    {
      ent->concentHistory.add(ent->concent);
    }

    // update concentration
    ent->refresh();
    
    //if (curStep<=10) cout << "Concen:: " << curStep << " conc = " << ent->deterministicConcent << "  " << ent->concent << endl;

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

    // if (Settings::getInstance()->printHistoryToFile->boolValue())
    // {
    //   ent->concentHistory.add(ent->concent);
    // }
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
    return; // #tkosc : should go below the following block ?

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
    // bool newRAC = (cycle->flow == 0.);
    //  SimReaction *minreac = cycle->reacDirs[0].first;

    // old way with only directions
    //  for (auto &reacDir : cycle->reacDirs)
    //  {
    //    auto reac = reacDir.first;
    //    bool dir = reacDir.second;

    //   if (dir != (reac->flowdir) || !(reac->enabled))
    //   { // wrong direction
    //     cycle->flow = 0.;
    //     continue;
    //   }
    //   if (reac->flow < cycle->flow)
    //   {
    //     cycle->flow = reac->flow;
    //     minreac = reac;
    //   }
    // }

    // new way by computing the total cycle flow for each entity of the PAC
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
        //flowPerEnt[ent] -= reac->flow; //
        flowPerEnt[ent] -= reac->deterministicFlow;
      }
      for (auto &ent : reac->products)
      {
        //flowPerEnt[ent] += reac->flow;
        flowPerEnt[ent] += reac->deterministicFlow;
      }
      // flowPerEnt[reac->reactant1] -= reac->flow;
      // flowPerEnt[reac->reactant2] -= reac->flow;
      // flowPerEnt[reac->product] += reac->flow;
      
    }
    
    
    // compute the flow of the cycle: the minimum of the flow of each entity, or 0 if negative
    cycle->flow = flowPerEnt[cycle->entities[0]]; // initialisation to a potential value, either <=0 or bigger than real value
    for (auto &ent : cycle->entities)
    {
      //cout << flowPerEnt[ent] << "  ";
      if (flowPerEnt[ent] < 0)
      {
        cycle->flow = 0.;
        break;
      }
      if (flowPerEnt[ent] < cycle->flow)
      {
        cycle->flow = flowPerEnt[ent];
      }
      if (ent->concent != 0.)
      {
        cycle->activity += 1./(ent->concent * (float) cycle->entities.size()) * flowPerEnt[ent];
      }
    }
    
   // cout << curStep << " -> cycle flow = " << cycle->flow << endl;;

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

    if (Settings::getInstance()->printHistoryToFile->boolValue())
    {
      // update history with flowPerEnt
      Array<float> RACflows;
      Array<float> RACposSpec;
      Array<float> RACnegSpec;
      Array<float> RACspec;
      for (auto &ent : cycle->entities)
      {
        RACflows.add(flowPerEnt[ent]);
        float specpos = 0.;
        float specneg = 0.;
        float spec = 0.;
        // positive specificity
        if (cycle->flow != 0.) // if cycle is off, +/- specificities are set to 0
        {
          if (otherPosFlowPerEnt[ent] != 0.)
            specpos = flowPerEnt[ent] / otherPosFlowPerEnt[ent];
          else
            specpos = 999.; // there shouldn't be a division by 0 above since otherPosFlowPerEnt at least contains flowPerEnt
                         // never too sure, I use dummy value to spot any unexpected behavior
          // negative specificity
          if (flowPerEnt[ent] != 0.)
            specneg = (flowPerEnt[ent] - otherNegFlowPerEnt[ent]) / flowPerEnt[ent];
          else
            specneg = 999.; // there shouldn't be a division by 0 above since condition cycle->flow != 0 prevents flowPerEnt to be 0
          // never too sure, I use dummy value to spot any unexpected behavior
        }
        spec = flowPerEnt[ent] / ( abs(flowPerEnt[ent]) + nonRACFlowPerEnt[ent]);
        RACposSpec.add(specpos);
        RACnegSpec.add(specneg);
        RACspec.add(spec);
      }
      // RAChistory[idPAC - 1]->hist.add(new RACSnapshot(cycle->flow, RACflows));
      RAChistory[idPAC - 1]->hist.add(new RACSnapshot(cycle->flow, RACflows, RACposSpec, RACnegSpec, RACspec));
      // cout<<"RAC "<<idPAC<<" history size "<<RAChistory[idPAC-1].size()<<endl;
    }

    PACsValues.add(cycle->flow);
    //cout << "curstep = " << curStep<<endl;
    //cout << "RAC Flow " << cycle->flow << "  " << cycle->toString() << endl;
    if (cycle->flow > 0)
    {
      cycle->wasRAC = true;
      // if (newRAC)
      // LOG("RAC " << idPAC << " from min reac " << minreac->name);
      if (cycle->flow > pacList->maxRAC)
        pacList->maxRAC = cycle->flow;
    }
    RACList.add(cycle->wasRAC);
  }
  // cout << "-" << endl;

  // if (Settings::getInstance()->printHistoryToFile->boolValue())
  // {
  //   // update history
  //   Array<float> concents;
  //   Array<float> flows;
  //   Array<float> racs;

  //   for (auto &ent : entities)
  //   {
  //     concents.add(ent->concent);
  //   }
  //   for (auto &reac : reactions)
  //   {
  //     flows.add(reac->flow);
  //   }
  //   for (auto &cycle : pacList->cycles)
  //   {
  //     racs.add(cycle->flow);
  //   }
  //   history.add(new Snapshot(curStep, concents, flows, racs));
  // }
  simNotifier.addMessage(new SimulationEvent(SimulationEvent::NEWSTEP, this, curStep, entityValues, {}, PACsValues, RACList));
  // listeners.call(&SimulationListener::newStep, this);
}

void Simulation::stop()
{
  finished->setValue(true);

  if (getUserListMode())
  {
    updateUserListFromSim();
  }
  state = Idle;

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
  while (!finished->boolValue() && !threadShouldExit())
  {
    nextStep();
  }

  if (!express)
    LOG("--------- End thread ---------");

  Array<float> entityValues;
  for (auto &ent : entities)
  {
    entityValues.add(ent->concent);
  }

  simNotifier.addMessage(new SimulationEvent(SimulationEvent::FINISHED, this, curStep, entityValues, {}, {}, {}));

  if (express)
  {
    // writeJSONConcents();
    return;
  }

  LOG("Record Concentration: " << recordConcent << " for entity " << recordEntity);
  if (recordDrawn < recordConcent)
    LOG("Record Drawn Concentration: " << recordDrawn << " for entity " << recordDrawnEntity);
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

  for (int idPAC0 = 0; idPAC0 < RAChistory.size(); idPAC0++)
  {
    int idPAC = idPAC0 + 1;
    String filename = "RAC" + String(idPAC) + ".csv";
    ofstream historyFile;
    historyFile.open(filename.toStdString(), ofstream::out | ofstream::trunc);
    // prepare csv to be readable by R
    historyFile << "Score,Step,RAC,";
    // test if no entities
    if (RAChistory[idPAC0]->hist.size() == 0)
    {
      LOG("RAC " + String(idPAC) + " history empty");
      historyFile.close();
      continue;
    }
    // for (int e = 0; e < RAChistory[idPAC0]->hist[0]->flows.size(); e++)
    for (auto &ent : RAChistory[idPAC0]->ents)
    {
      // historyFile << "ent" << e + 1 << ",prop" << e + 1 << ",";
      historyFile << ent->name << ",spec+_" << ent->name << ",spec-_" << ent->name << ",spec_" << ent->name;
    }
    historyFile << endl;
    int i = 0;
    for (auto &snap : RAChistory[idPAC0]->hist)
    {
      i++;
      if (i == 1)
        historyFile << RAChistory[idPAC0]->pacScore << ",";
      else
        historyFile << ",";
      historyFile << i << "," << snap->rac << ",";
      for (int e = 0; e < snap->flows.size(); e++)
      {
        historyFile << snap->flows[e] << ",";
        historyFile << snap->posSpecificities[e] << ",";
        historyFile << snap->negSpecificities[e] << ",";
        historyFile << snap->specificity[e];
      }
      historyFile << endl;
    }
    historyFile.close();
  }
  LOG("RAC History written to files RACi.csv");

  // store concentration all entity concentrations history to csv file
  String concentFilename = "./concentrationDynamic.csv";
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
  for (int s = 0; s < (nSteps - 1); s++)
  {
    float fs = (float)s;
    float time = fs * dt->floatValue();
    outfile << time << ",i_run,";
    int c = 0;
    for (auto &ent : entities)
    {
      string comma = (c == (entities.size() - 1)) ? "" : ",";
      outfile << ent->concentHistory[s] << comma;
      c++;
    }
    outfile << endl;
  }
  // close concentration file output
  outfile.close();
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
    ent.getDynamicObject()->setProperty("Start", e->startConcent);
    ent.getDynamicObject()->setProperty("End", e->concent);
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

  /*if (liveUpdate->boolValue())
  {
    if (p == totalTime || p == pointsDrawn)
    {
      start();
    }
  }
  */
}


void Simulation::initPhasePlane()
{
  PhasePlane * pp = new PhasePlane();
}
