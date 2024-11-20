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
	id = data.getProperty("id", id);
	concent = data.getProperty("concent", concent);
	startConcent = data.getProperty("startConcent", startConcent);
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
}


SimEntity::SimEntity(Entity* e) :
	entity(e)
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
	name = entity->niceName;
	enabled = entity->enabled->boolValue();
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

var SimEntity::toJSONData()
{
	var data = new DynamicObject();
	data.getDynamicObject()->setProperty("name", name);
	data.getDynamicObject()->setProperty("color", SimulationHelpers::color2JSON(color));
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
	for (auto& i : composition) comp.append(i);
	data.getDynamicObject()->setProperty("composition", comp);
	return data;
}

SimEntity::~SimEntity()
{
}

void SimEntity::increase(float incr)
{
	change += incr;
}

void SimEntity::decrease(float decr)
{
	change -= decr;
}

void SimEntity::refresh()
{
	concent = jmax(0.f, concent + change);
	change = 0.f;
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
	return "[Entity " + name + " : " + String(concent) + "]";
}