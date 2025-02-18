/*
  ==============================================================================

	SimReaction.cpp
	Created: 29 Sep 2024 11:09:45am
	Author:  bkupe

  ==============================================================================
*/

#include "SimReaction.h"
#include "Reaction.h"
#include "Entity.h"
#include "SimEntity.h"
#include "Simulation.h"

SimReaction::SimReaction(Reaction *r)
{
	updateFromReaction(r);
}

SimReaction::SimReaction(SimEntity *r1, SimEntity *r2, SimEntity *p, float aRate, float dRate, float barrier) : reaction(nullptr),
																												assocRate(aRate),
																												dissocRate(dRate),
																												energy(barrier)
{
	reactants.add(r1);
	reactants.add(r2);
	products.add(p);
	autoSetName();
}

SimReaction::SimReaction(Array<SimEntity *> mReac, Array<SimEntity *> mProd, float aRate, float dRate, float barrier) : reaction(nullptr),
																														assocRate(aRate),
																														dissocRate(dRate),
																														energy(barrier)
{
	for (auto &r : mReac)
		reactants.add(r);
	for (auto &p : mProd)
		products.add(p);
	autoSetName();
}

void SimReaction::updateFromReaction(Reaction *r)
{
	reaction = r;
	assocRate = r->assocRate->floatValue();
	dissocRate = r->dissocRate->floatValue();
	energy = r->energy->floatValue();
	name = r->niceName; // name from the original reaction
	enabled = r->enabled->boolValue();
	generatedFromUserList = true;
	reactants.clear();
	products.clear();

	for (auto c : r->reactants->controllables)
	{
		Entity *e = ((TargetParameter *)c)->getTargetContainerAs<Entity>();

		if (e == nullptr)
		{
			LOGWARNING("Reactant entity target is null, not adding to sim reactant");
			continue;
		}

		if (SimEntity *se = Simulation::getInstance()->getSimEntityForName(e->niceName))
		{
			reactants.add(se);
		}
		else
		{
			LOGWARNING("No SimEntity for reactant in reaction");
			constructionFailed = true;
			continue;
		}
	}

	for (auto c : r->products->controllables)
	{
		Entity *e = ((TargetParameter *)c)->getTargetContainerAs<Entity>();

		if (e == nullptr)
		{
			LOGWARNING("Product entity target is null, not adding to sim product");
			continue;
		}

		if (SimEntity *se = Simulation::getInstance()->getSimEntityForName(e->niceName))
		{
			products.add(se);
		}
		else
		{
			LOGWARNING("No SimEntity for product in reaction");
			constructionFailed = true;
			continue;
		}
	}
}

SimReaction::SimReaction(var data)
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

	bool arrayMode = false;

	Simulation *simul = Simulation::getInstance();
	SimEntity *reactant1;
	// test whether the file uses old or new conventions, put in arrayMode
	if (data.getDynamicObject()->hasProperty("reactant1"))
	{
		reactant1 = simul->getSimEntityForName(data["reactant1"]);
		if (reactant1 == nullptr)
		{
			LOGWARNING("reactant1 null for SimReaction");
			constructionFailed = true;
			return;
		}
		arrayMode = false;
	}
	else
	{
		arrayMode = true;
	}

	if (!arrayMode)
	{
		SimEntity *reactant2;
		SimEntity *product;
		// to change on same model
		if (data.getDynamicObject()->hasProperty("reactant2"))
		{
			reactant2 = simul->getSimEntityForName(data["reactant2"]);
			if (reactant2 == nullptr)
			{
				LOGWARNING("reactant2 null for SimReaction");
				constructionFailed = true;
				return;
			}
		}
		else
		{
			LOGWARNING("No reactant2 for SimReaction");
			constructionFailed = true;
			return;
		}

		if (data.getDynamicObject()->hasProperty("product"))
		{
			product = simul->getSimEntityForName(data["product"]);
			if (product == nullptr)
			{
				LOGWARNING("Product null for SimReaction");
				constructionFailed = true;
				return;
			}
		}
		else
		{
			LOGWARNING("No product for SimReaction");
			constructionFailed = true;
			return;
		}
		reactants.add(reactant1);
		reactants.add(reactant2);
		products.add(product);
	}
	else
	{ // array mode
		if (data.getDynamicObject()->hasProperty("reactants"))
		{
			auto reactantsData = data["reactants"].getArray();
			for (auto &coord : *reactantsData)
			{
				SimEntity *reactant = simul->getSimEntityForName(coord["ent"]);
				if (reactant == nullptr)
				{
					LOGWARNING("Reactants null for Simreaction");
					constructionFailed = true;
					return;
				}
				reactants.add(reactant);
			}
		}
		else
		{
			LOGWARNING("No reactants for Simreaction");
			constructionFailed = true;
			return;
		}

		if (data.getDynamicObject()->hasProperty("products"))
		{

			auto productsData = data["products"].getArray();
			for (auto &coord : *productsData)
			{
				SimEntity *product = simul->getSimEntityForName(coord["ent"]);
				if (product == nullptr)
				{
					// LOGWARNING("No product for reaction");
					constructionFailed = true;
					return;
				}
				products.add(product);
			}
		}
		else
		{
			constructionFailed = true;
			return;
		}
	}

	if (data.getDynamicObject()->hasProperty("name"))
		name = data["name"];

	if (data.getDynamicObject()->hasProperty("assocRate"))
		assocRate = data["assocRate"];

	if (data.getDynamicObject()->hasProperty("dissocRate"))
		dissocRate = data["dissocRate"];
  
	if (data.getDynamicObject()->hasProperty("idSAT"))
		idSAT = data["idSAT"];

	//if reaction with same name exists, point to it
	reaction = ReactionManager::getInstance()->getReactionFromName(name);
}

var SimReaction::toJSONData()
{
	var data = new DynamicObject();
	// data.getDynamicObject()->setProperty("reactant1", reactant1->name);
	// data.getDynamicObject()->setProperty("reactant2", reactant2->name);
	// data.getDynamicObject()->setProperty("product", product->name);
	// to array
	var reactantsData;
	for (auto r : reactants)
	{
		var coord = new DynamicObject();
		coord.getDynamicObject()->setProperty("ent", r->name);
		reactantsData.append(coord);
	}
	data.getDynamicObject()->setProperty("reactants", reactantsData);

	var productsData;
	for (auto p : products)
	{
		var coord = new DynamicObject();
		coord.getDynamicObject()->setProperty("ent", p->name);
		productsData.append(coord);
	}
	data.getDynamicObject()->setProperty("products", productsData);

	data.getDynamicObject()->setProperty("name", name);

	data.getDynamicObject()->setProperty("assocRate", assocRate);
	data.getDynamicObject()->setProperty("dissocRate", dissocRate);
	data.getDynamicObject()->setProperty("idSAT", idSAT);

	return data;
}

SimReaction::~SimReaction()
{
}

bool SimReaction::containsReactant(SimEntity *e)
{
	for (auto r : reactants)
	{
		if (r == e)
			return true;
	}
	return false;
}

bool SimReaction::containsProduct(SimEntity *e)
{

	for (auto p : products)
	{
		if (p == e)
			return true;
	}
	return false;
}

bool SimReaction::contains(SimEntity *e)
{
	return (containsReactant(e) || containsProduct(e));
}

int SimReaction::stoechiometryOfEntity(SimEntity *e)
{
	int st = 0;
	for (auto &sre : reactants)
		if (sre == e)
			st--;
	for (auto &sre : products)
		if (sre == e)
			st++;
	return st;
}

void SimReaction::computeRate(bool noBarrier, bool noFreeEnergy)
{
	// GA+GB
	// float energyLeft = noFreeEnergy ? 0.f : reactant1->freeEnergy + reactant2->freeEnergy;
	float energyLeft = 0.f;
	if (!noFreeEnergy)
	{
		for (auto r : reactants)
		{
			energyLeft += r->freeEnergy;
		}
	}
	// GAB
	// float energyRight = noFreeEnergy ? 0.f : product->freeEnergy;
	float energyRight = 0.f;
	if (!noFreeEnergy)
	{
		for (auto p : products)
		{
			energyRight += p->freeEnergy;
		}
	}
	// total energy G* of the reaction: activation + max of GA+GB and GAB.
	float energyStar = (noBarrier ? 0.f : energy) + jmax(energyLeft, energyRight);
	// k1=exp(GA+GB-G*)
	assocRate = exp(energyLeft - energyStar);
	// k2=exp(GAB-G*)
	dissocRate = exp(energyRight - energyStar);
}





void SimReaction::computeBarrier()
{
	float energyLeft = 0.f;
	for (auto r : reactants)
	{
		energyLeft += r->freeEnergy;
	}
	float energyRight = 0.f;
	for (auto p : products)
	{
		energyRight += p->freeEnergy;
	}

	// we use that assocRate is exp(energyLeft - energyStar) to compute energyStar
	float energyStar = energyLeft - log(assocRate);
	// we use that energyStar = energy + jmax(energyLeft, energyRight); to compute energy
	energy = energyStar - jmax(energyLeft, energyRight);
}

// void SimReaction::importFromManual()
//{
//     if (reaction == nullptr)
//     {
//         LOGERROR("Reaction is null here, should not happen");
//         return;
//     }
//
//     assocRate = reaction->assocRate->floatValue();
//     dissocRate = reaction->dissocRate->floatValue();
//     energy = reaction->energy->floatValue();
//     enabled = reaction->shouldIncludeInSimulation();
//     name = reaction->niceName;
// }

void SimReaction::autoSetName()
{
	name = "";
	// reactant1->name + "+" + reactant2->name + "=" + product->name;
	bool first = true;
	for (auto &ent : reactants)
	{
		if (!first)
		{
			name += "+";
		}
		name += ent->name;

		first = false;
	}
	name += "=";
	first = true;
	for (auto &ent : products)
	{
		if (!first)
		{
			name += "+";
		}
		name += ent->name;
		first = false;
	}
}
