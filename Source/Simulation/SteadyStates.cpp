#include "SteadyStates.h"
#include "Simulation.h"
#include "Settings.h"
#include <regex>
#include <stack>
#include <cctype>

using namespace std;



///////////////////////////////////////////////////////////
/////////////////// STEADY STATE //////////////////////////
///////////////////////////////////////////////////////////


SteadyStates::SteadyStates(var data, Simulation *simul)
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

	if (data.getDynamicObject()->hasProperty("entities"))
	{
		Array<var> *ents = data.getDynamicObject()->getProperty("entities").getArray();
		for (auto &ent : *ents)
		{
			SimEntity *e = simul->getSimEntityForName(ent["ent"]);
			if (e == nullptr)
			{
				constructionFailed = true;
				LOGWARNING("SteadyStates construction failed: entity " + ent["ent"].toString() + " not found");
				return;
			}
			entities.add(e);
		}
	}

	if (data.getDynamicObject()->hasProperty("reacDirs"))
	{
		Array<var> *reacds = data.getDynamicObject()->getProperty("reacDirs").getArray();
		for (auto &reacd : *reacds)
		{
			SimReaction *r = simul->getSimReactionForName(reacd["reac"]);
			if (r == nullptr)
			{
				constructionFailed = true;
				LOGWARNING("SteadyStates construction failed: reaction " + reacd["reac"].toString() + " not found");
				return;
			}
			reacDirs.add(make_pair(r, reacd["dir"]));
		}
	}
	//cout << "SteadyStates loaded: " << toString() << " with " << entities.size() << " entities and " << reacDirs.size() << " reactions" << endl;
}




var SteadyStates::toJSONData()
{
	var data = new DynamicObject();

	var ents;
	for (auto &e : entities)
	{
		var coord = new DynamicObject();
		coord.getDynamicObject()->setProperty("ent", e->name);
		ents.append(coord);
	}
	data.getDynamicObject()->setProperty("entities", ents);

	var reacds;
	for (auto &rd : reacDirs)
	{
		var coord = new DynamicObject();
		coord.getDynamicObject()->setProperty("reac", rd.first->name);
		coord.getDynamicObject()->setProperty("dir", rd.second);
		reacds.append(coord);
	}
	data.getDynamicObject()->setProperty("reacDirs", reacds);

	return data;
}





///////////////////////////////////////////////////////////
///////////////// STEADY STate List ////////////////////////
///////////////////////////////////////////////////////////





SteadyStateslist::~SteadyStateslist()
{
	stopThread(500);
}

void SteadyStateslist::printSteadyStates()
{
/// ***	
}



void SteadyStateslist::clear()
{
	/// ***
}







void SteadyStateslist::run()
{
	/// ***
}





var SteadyStateslist::toJSONData()
{
	 var data = new DynamicObject();
	// // save cycles
	// var cyclesData;
	// for (auto &c : cycles)
	// {
	// 	cyclesData.append(c->toJSONData());
	// }
	// data.getDynamicObject()->setProperty("cycles", cyclesData);
	// // save CACs
	// var CACsData;
	// for (auto &c : CACs)
	// {
	// 	CACsData.append(CACtoJSON(c));
	// }
	// data.getDynamicObject()->setProperty("CACs", CACsData);
	 return data;
}

void SteadyStateslist::fromJSONData(var data)
{
	// clear();
	// // load cycles
	// if (!data.getDynamicObject()->hasProperty("cycles") || !data["cycles"].isArray())
	// {
	// 	LOGWARNING("wrong PAC format in SteadyStateslist JSON data");
	// 	return;
	// }
	// Array<var> *cyclesData = data["cycles"].getArray();
	// for (auto &c : *cyclesData)
	// {
	// 	PAC *pac = new PAC(c, simul);
	// 	cycles.add(pac);
	// }
	// simul->PACsGenerated = true;
	// // load CACs
	// if (!data.getDynamicObject()->hasProperty("CACs") || !data["CACs"].isArray())
	// {
	// 	LOGWARNING("Wrong CAC format in SteadyStateslist JSON data");
	// 	return;
	// }
	// Array<var> *CACsData = data["CACs"].getArray();
	// for (auto &c : *CACsData)
	// {
	// 	CACType cac = JSONtoCAC(c);
	// 	CACs.add(cac);
	// 	if (cac.first.size() == 1)
	// 		basicCACs.add(*(cac.first.begin()));
	// }
}
