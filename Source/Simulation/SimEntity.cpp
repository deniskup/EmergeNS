/*
  ==============================================================================

	SimEntity.cpp
	Created: 29 Sep 2024 11:09:38am
	Author:  bkupe

  ==============================================================================
*/

#include "SimEntity.h"
#include "Entity.h"
#include "SimReaction.h"
#include "Space.h"

SimEntity::SimEntity(var data)
{
	if (data.isVoid())
	{
		constructionFailed = true;
		return;
	}

	if (data.getDynamicObject() == nullptr)
	{
		constructionFailed = true;
		return;
	}


	if (data.getDynamicObject()->hasProperty("name"))
	{
		name=data.getProperty("name","unknown");
	}
	else
	{
		LOGWARNING("No name for Entity");
		constructionFailed = true;
		return;
	}

	if (data.getDynamicObject()->hasProperty("color"))
		color = SimulationHelpers::JSON2Color(data.getDynamicObject()->getProperty("color"));

	primary = data.getProperty("primary", primary);
	chemostat = data.getProperty("chemostat", chemostat);
	id = data.getProperty("id", id);
	//concent = data.getProperty("concent", concent);
	//startConcent = data.getProperty("startConcent", startConcent);
  
  concent.resize(Space::getInstance()->nPatch);
  for (int k=0; k<concent.size(); k++)
    concent.set(k, 0.);
  if (data.getDynamicObject()->hasProperty("concent"))
  {
    if (data.getDynamicObject()->getProperty("concent").isArray())
    {
      Array<var> * arrv = data.getDynamicObject()->getProperty("concent").getArray();
      int c=-1;
      for (auto & v : *arrv)
      {
        c++;
        String patchid = v["patch"];
        float conc = v["concent"];
        concent.set(c, conc);
      }
    }
  }
  
  startConcent.resize(Space::getInstance()->nPatch);
  for (int k=0; k<startConcent.size(); k++)
    startConcent.set(k, 0.);
  if (data.getDynamicObject()->hasProperty("startConcent"))
  {
    if (data.getDynamicObject()->getProperty("startConcent").isArray())
    {
      Array<var> * arrv = data.getDynamicObject()->getProperty("startConcent").getArray();
      int c=-1;
      for (auto & v : *arrv)
      {
        c++;
        String patchid = v["patch"];
        float conc = v["startConcent"];
        startConcent.set(c, conc);
      }
    }
  }
  /*
  cout << "sanity check for entity " << name << endl;
  for (auto & c : startConcent)
    cout << c << " ";
  cout << endl;
*/
	creationRate = data.getProperty("creationRate", creationRate);
	destructionRate = data.getProperty("destructionRate", destructionRate);
	freeEnergy = data.getProperty("freeEnergy", freeEnergy);
	level = data.getProperty("level", level);
	draw = data.getProperty("draw", draw);

	var compData = data.getProperty("composition", var());
	for (int i = 0; i < compData.size(); i++)
	{
		int val = compData[i].isObject() ? (int)compData[i].getProperty("coord", 0) : (int)compData[i];
		composition.add(val);
	}

	//if entity of same name exists, point to it
	entity = EntityManager::getInstance()->getEntityFromName(name);

	// else
	// {
	// 	LOGWARNING("No entity found for SimEntity " + name);
	// }
  
  
  /*
  cout << "SimEntity Constructor, loaded entity with name " << name << endl;
  int p=0;
  for (auto & c : startConcent)
  {
    cout << "patch #" << p << " -> startconc = " << c << endl;
    p++;
  }
  p=0;
  for (auto & c : concent)
  {
    cout << "patch #" << p << " -> concent = " << c << endl;
    p++;
  }
  */
}


SimEntity::SimEntity(Entity* e)
{
	updateFromEntity(e);
}


SimEntity::SimEntity(bool isPrimary, float concent, float cRate, float dRate, float freeEnergy) :
	primary(isPrimary),
	concent(concent),
	startConcent(concent),
	creationRate(cRate),
	destructionRate(dRate),
	freeEnergy(freeEnergy),
	name("New entity"),
	entity(nullptr)
{
}

SimEntity::SimEntity(const SimEntity* other)
{
    jassert(other != nullptr);

    name = other->name;
    entity = other->entity; // shallow copy 
    color = other->color;
    primary = other->primary;
    chemostat = other->chemostat;
    id = other->id;

    concent = other->concent;
    deterministicConcent = other->deterministicConcent;
    startConcent = other->startConcent;
    previousConcent = other->previousConcent;

    creationRate = other->creationRate;
    destructionRate = other->destructionRate;
    freeEnergy = other->freeEnergy;

    change = other->change;
    deterministicChange = other->deterministicChange;

    reached = other->reached;
    isolated = other->isolated;
    enabled = other->enabled;
    generatedFromUserList = other->generatedFromUserList;
    toImport = other->toImport;

    level = other->level;
    draw = other->draw;

    composition = other->composition;
    idSAT = other->idSAT;

}


unique_ptr<SimEntity> SimEntity::clone() const
{
    return std::make_unique<SimEntity>(this);
}



void SimEntity::updateFromEntity(Entity *e)
{
	if(e==nullptr)
	{
		constructionFailed = true;
		return;
	}
	entity = e;
	e->simEnt=this;
	//startConcent = e->startConcent->floatValue();
	//concent = e->concent->floatValue();
  startConcent.set(e->patchid, e->startConcent->floatValue());
  concent.set(e->patchid, e->concent->floatValue());
	creationRate = e->creationRate->floatValue();
	destructionRate = e->destructionRate->floatValue();
	freeEnergy = e->freeEnergy->floatValue();
	enabled = e->enabled->boolValue();
	color = e->itemColor->getColor();
	level = e->level;
	composition = e->composition;
	draw = e->draw->boolValue();
	primary = e->primary->boolValue();
	chemostat = e->chemostat->boolValue();
	name = e->niceName;
	enabled = e->enabled->boolValue();
	generatedFromUserList = true;
  // synchronize space grid with entity change
  // in an ugly way by manually calling the trigger button of space instance
  // better way would be use listeners instead ?
  // Space::getInstance()->initGridAtStartValues->trigger(); // #TODO find another solution
}

var SimEntity::toJSONData()
{
	var data = new DynamicObject();
	data.getDynamicObject()->setProperty("name", name);
	data.getDynamicObject()->setProperty("color", SimulationHelpers::color2JSON(color));
	data.getDynamicObject()->setProperty("primary", primary);
	data.getDynamicObject()->setProperty("chemostat", chemostat);
	data.getDynamicObject()->setProperty("id", id);
  
  var vconc;
  for (int k=0; k<concent.size(); k++)
  {
    var v = new DynamicObject();
    v.getDynamicObject()->setProperty("patch", k);
    v.getDynamicObject()->setProperty("concent", concent[k]);
    vconc.append(v);
  }
	data.getDynamicObject()->setProperty("concent", vconc);
  
  var vstartconc;
  for (int k=0; k<startConcent.size(); k++)
  {
    var v = new DynamicObject();
    v.getDynamicObject()->setProperty("patch", k);
    v.getDynamicObject()->setProperty("startConcent", startConcent[k]);
    vstartconc.append(v);
  }
  data.getDynamicObject()->setProperty("startConcent", vstartconc);
	//data.getDynamicObject()->setProperty("startConcent", startConcent);
	data.getDynamicObject()->setProperty("creationRate", creationRate);
	data.getDynamicObject()->setProperty("destructionRate", destructionRate);
	data.getDynamicObject()->setProperty("freeEnergy", freeEnergy);
	data.getDynamicObject()->setProperty("level", level);
	data.getDynamicObject()->setProperty("draw", draw);


	var comp;
	for (auto& i : composition) comp.append(i);
	data.getDynamicObject()->setProperty("composition", comp);
	return data;
}

SimEntity::~SimEntity()
{
}

void SimEntity::increase(int patchID, float incr)
{
  change.set(patchID, change[patchID] + incr);
}

void SimEntity::deterministicIncrease(int patchID, float incr)
{
  //deterministicChange[patchID] += incr;
  deterministicChange.set(patchID, deterministicChange[patchID] + incr);

}

void SimEntity::decrease(int patchID, float decr)
{
	//change[patchID] -= decr;
  change.set(patchID, change[patchID] - decr);

}

void SimEntity::deterministicDecrease(int patchID, float decr)
{
  //deterministicChange[patchID] -= decr;
  deterministicChange.set(patchID, deterministicChange[patchID] - decr);
}

void SimEntity::refresh()
{
  for (int i=0; i<concent.size(); i++) // size is number of pacthes
  {
    if (!chemostat)
    {
      concent.set(i, jmax(0.f, concent[i] + change[i]));
      deterministicConcent.set(i, jmax(0.f, deterministicConcent[i] + deterministicChange[i]));
    }
    change.set(i, 0.f);
    deterministicChange.set(i, 0.f);
  }
}

void SimEntity::nameFromCompo()
{
	name = "";
	for (auto& i : composition)
	{
		name += String(i);
	}
}

String SimEntity::toString() const
{
	//return "[Entity " + name + " : " + String(concent) + "]";
  String tostr = "[Entity " + name + " : [";
  for (int k=0; k<concent.size(); k++)
  {
    String comma = (k==concent.size()-1 ? "" : " ; ");
    tostr += String(concent[k]) + comma;
  }
  tostr += "]";
  return tostr;
}
