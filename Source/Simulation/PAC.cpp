#include "PAC.h"
using namespace std;



PAC::PAC(var data, Simulation *simul)
{
  if (data.isVoid())
    return;
  if (data.getDynamicObject() == nullptr)
    return;

  if (data.getDynamicObject()->hasProperty("entities"))
  {
    Array<var> *ents = data.getDynamicObject()->getProperty("entities").getArray();
    for (auto &ent : *ents)
    {
      entities.add(simul->getSimEntityForID(ent["ent_id"]));
    }
  }

  if (data.getDynamicObject()->hasProperty("reacDirs"))
  {
    Array<var> *reacds = data.getDynamicObject()->getProperty("reacDirs").getArray();
    for (auto &reacd : *reacds)
    {
      reacDirs.add(make_pair(simul->getSimReactionForID(reacd["reac_id"]), reacd["dir"]));
    }
  }
}

var PAC::toJSONData()
{
  var data = new DynamicObject();

  var ents;
  for (auto &e : entities)
  {
    var coord = new DynamicObject();
    coord.getDynamicObject()->setProperty("ent_id", e->id);
    ents.append(coord);
  }
  data.getDynamicObject()->setProperty("entities", ents);

  var reacds;
  for (auto &rd : reacDirs)
  {
    var coord = new DynamicObject();
    coord.getDynamicObject()->setProperty("reac_id", rd.first->idSAT);
    coord.getDynamicObject()->setProperty("dir", rd.second);
    reacds.append(coord);
  }
  data.getDynamicObject()->setProperty("reacDirs", reacds);

  return data;
}

String PAC::toString()
{
  String res;
  for (auto &rd : reacDirs)
  {
    auto r = rd.first;
    bool d = rd.second;
    auto p = r->product;
    auto r1 = r->reactant1;
    auto r2 = r->reactant2;
    String plus = "+";
    String r1name = r1->name;
    String r2name = r2->name;
    if (!entities.contains(r1))
    {
      plus = "";
      r1name = "";
    }
    if (!entities.contains(r2))
    {
      plus = "";
      r2name = "";
    }
    if (d)
    { // 1->2
      res += r->product->name + "->" + r1name + plus + r2name + " ";
    }
    else
    { // 2->1
      res += r1name + plus + r2name + "->" + r->product->name + " ";
    }
  }
  return res;
}

bool PAC::includedIn(PAC *pac, bool onlyEnts)
{
  for (auto &e : entities)
  {
    if (!pac->entities.contains(e))
      return false;
  }
  if (onlyEnts)
    return true;
  // test reactions
  for (auto &rd : reacDirs)
  {
    if (!pac->reacDirs.contains(rd))
      return false;
  }
  return true;
}


void PAClist::addCycle(PAC *newpac)
{
  // we only test if is is included in existing one, other direction is taken care of by SAT solver
  for (int i = 0; i < cycles.size(); i++)
  {
    if (newpac->includedIn(cycles[i], includeOnlyWithEntities))
    {
      cycles.remove(i);
    }
  }
  cycles.add(newpac);
}

void PAClist::printPACs()
{
  LOG("PACS computed");
  for (auto pac : cycles)
  {
    cout << pac->toString() << endl;
  }
}


void PAClist::clear()
{
  cycles.clear();
  PACsGenerated = false;
  maxRAC = 0.;
}
