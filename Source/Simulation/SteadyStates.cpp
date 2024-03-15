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


// input term should be of the form "k0*ci*...*cj + k1*ci*...*cj"
string PartialDerivate(string term, string var)
{

  ///cout << "input term (to derivate wrt to " << var <<  ") : " << term << endl;
  
  std::string partial = "";

  // get ready for the while loop
  std::stringstream sterm(term);
  std::string subterm = "";

  while(std::getline(sterm, subterm, '+')) // separate each term of the input string 
  {
	///cout << "\tsubterm " << subterm << endl;
	if (subterm.find(var)==subterm.npos) 
	{
		///cout << "\tno dependence on " << var << endl;
		partial += "0+"; // remove case where derivate = 0 straight away
		///cout << "\t\t" << partial << endl;
		continue;
	}

  	stringstream ssubterm(subterm);
  	string fac = "";

	// find power dependence of current subterm wrt to variable
  	int pow=0;
  	while(getline(ssubterm, fac, '*'))
    {
    	if (fac==var) pow++;
    }

	///cout << "\tpower equals " << pow << endl;
    
    // init partial derivate of current subterm
  	string subpartial = to_string(pow) + "*" + subterm;

	// reduce power of var by 1, by chanchin var into a '1'
	subpartial.replace(subpartial.find(var.c_str()), var.size(), "1");

  	// if (pow==1)
    // {
    // 	partial.erase(partial.find_first_of(var.c_str()), 1);   
    // }
  	// else if (pow>1)
  	// {
    // 	for (int k=1; k<=(pow-1); k++) // works if pow > 1
	// 	{
    //   partial.erase(partial.find_first_of(var.c_str()), 1);
    // 	}
	// }
   
  // remove subsequent double products
  while (subpartial.find("**")!=subpartial.npos) subpartial.replace(subpartial.find("**"), 2, "*");
  
  // remove first character and last characters if equal to '*'
  //if (subpartial.at(0)=='*') subpartial.erase(0, 1);
  //if (subpartial[subpartial.size()-1]=='*') subpartial.erase(subpartial.size()-1, 1);

  // add subpartial to total partial derivative
  partial += subpartial + "+";
  cout << "\t\t" << partial << endl;
  
}

// clean last character
if (partial[partial.size()-1]=='+') partial.erase(partial.size()-1, 1);

///cout << "output term : " << partial << endl << endl;

return partial;

} 




void SteadyStateslist::computeJacobiMatrix()
{
	//compute Jacobian matrix

	// affect id to entities in reactions
	simul->affectSATIds();

	// Init a vector<string> of size #entites
	vector<string> dcdt(simul->entities.size());

	cout << "simu  has " << simul->entities.size() << " entites" << endl;


	for (auto& r : simul->reactions)
	{
		// retrieve stoechiometry vector
		//cout << "In reaction " << r->idSAT << endl;
		map<int, int> stoec;
		for (auto& reactant : r->reactants)
		{
			//cout << "\thas reactant " << reactant->idSAT << endl;
			stoec[reactant->idSAT]--;
		}
		for (auto& product : r->products)
		{
			//cout << "\thas product " << product->idSAT << endl;
			stoec[product->idSAT]++;
		}


		// build string factor associated to current forward reaction
		string fac_forward = to_string(r->assocRate) + "*";

		for (auto& [id, st] : stoec)
		{
			if (st>0) continue; // only keep reactants
			for (int k=0; k<abs(st); k++) fac_forward +=  "c" + to_string(id) + "*";
		}

		// remove last character which might be a "*"
		  if (fac_forward[fac_forward.size()-1]=='*') fac_forward.erase(fac_forward.size()-1, 1);

		//cout << "\tforward factor associated : " << fac_forward << endl;


		// build string factor associated to current backward reaction, is reversible
		string fac_backward = "";
		
		if (r->isReversible)
		{
			fac_backward = to_string(r->dissocRate) + "*";
			for (auto& [id, st] : stoec)
			{
				if (st<0) continue; // only keep reactants
				for (int k=0; k<abs(st); k++) fac_backward +=  "c" + to_string(id) + "*";
			}

			// remove last character which might be a "*"
			if (fac_backward[fac_backward.size()-1]=='*') fac_backward.erase(fac_backward.size()-1, 1);

			//cout << "\tbackward factor associated : " << fac_backward << endl;
		}

		// add forward or backward factors to time derivate of concentrations
		for (auto& [id, st] : stoec)
		{
			if (st<0) // reactant case
			{
				dcdt[id] += to_string(st) + "*" + fac_forward + "+";
				if (r->isReversible) dcdt[id] += to_string(abs(st)) + "*" + fac_backward + "+";
			}
			if (st>0) // product case
			{
				dcdt[id] += to_string(st) + "*" + fac_forward + "+";
				if (r->isReversible) dcdt[id] += to_string(-st) + "*" + fac_backward + "+";
			}
		}
	} // end reaction loop

	// remove last character '+'
	for (auto& der : dcdt)
	{
		if (der[der.size()-1]=='*') der.erase(der.size()-1, 1);
		//cout << der << endl;
	}


	// calculate partial derivative wrt c_i for each element of vector dcdt
	for (auto& cpoint : dcdt)
	{
		cout << cpoint << endl;
		// loop over each entity
		for (unsigned int ie=0; ie<dcdt.size(); ie++)
		{
			string var = "c" + to_string(ie);
			string partial = PartialDerivate(dcdt[ie], var);
			cout << "\twrt c" + to_string(ie) + "  " + partial << endl;
		}

	}






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
