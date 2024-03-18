#include "SteadyStates.h"
#include "Simulation.h"
#include "Settings.h"
#include <regex>
#include <stack>
#include <cctype>

using namespace std;





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
	steadyStates.clear();
}







void SteadyStateslist::run()
{
	//compute steady states
}


void SteadyStateslist::computeWithZ3()
{
	//compute steady states

}







void SteadyStateslist::computeJacobiMatrix()
{
	

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
