#include "SteadyStates.h"
#include "Simulation.h"
#include "Settings.h"
#include <regex>
#include <stack>
#include <cctype>
#include "PAC.h" //for ParseModel

using namespace std;
//using Eigen::MatrixXd;



///////////////////////////////////////////////////////////
///////////////// out of class functions /////////////////
///////////////////////////////////////////////////////////






///////////////////////////////////////////////////////////
///////////////// SteadyStatelist METHODS /////////////////
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

void SteadyStateslist::computeSteadyStates(){
	startThread();
}

void SteadyStateslist::run()
{
	// mark beginning of computation
	simul->isComputing = true;
	simul->shouldStop = false;
	// measure time
	uint32 startTime = Time::getMillisecondCounter();


	computeWithZ3(); // search for stationnary points

	// print z3 execution time
	simul->isComputing = false;
	if (simul->shouldStop)
	{
		LOG("Computation stopped manually");
		simul->shouldStop = false;
	}
	LOG("Execution time: " << String(Time::getMillisecondCounter() - startTime) << " ms");
	simul->shouldUpdate = true;
	// update the parameters of the simulation in the UI
	simul->simNotifier.addMessage(new Simulation::SimulationEvent(Simulation::SimulationEvent::UPDATEPARAMS, simul));

	// stability of stationnary points

	computeJacobiMatrix(); // formally calculate jacobi matrix of chemical reaction network

	keepStableSteadyStatesOnly();

}



void SteadyStateslist::setZ3path()
{
	if (z3path != "") // already has been done
		return;
	vector<string> z3commands;
	z3commands.push_back("z3");
	z3commands.push_back(Settings::getInstance()->pathToz3->stringValue().toStdString());

	for (int z3id = 0; z3id <= 1; z3id++)
	{

		z3path = z3commands[z3id];
		string z3command = z3path + " z3test.smt2 > testResult.txt";
		ofstream testFile;
		testFile.open("z3test.smt2", ofstream::out | ofstream::trunc);
		testFile << "(assert true)" << endl;
		testFile << "(check-sat)" << endl;
		testFile.close();
		const int satReturnValue = system(z3command.c_str());
		ifstream sol_file("testResult.txt");
		string testSat;

		sol_file >> testSat;

		if (testSat == "sat")
		{
			break;
		}

		if (z3id == 0)
			LOG("z3 not accessible directly, using path specified in Settings: " + z3commands[1]);
		else
		{
			LOG("z3 path failed, aborting");
			return;
		}
	}
	// add timeout
	int timeout=Settings::getInstance()->z3timeout->intValue();
	if(timeout>0){
		z3path += " -t:" + to_string(timeout);
	}
}

void SteadyStateslist::computeWithZ3()
{
	// compute steady states
	setZ3path();
	LOG("Computing steady states with Z3...");
	// set idSAT for entities and reactions
	// to be changed to simul->affectSATIds();
	int idSAT = 0;
	for (auto &e : simul->entities)
	{
		idSAT++;
		e->idSAT = idSAT;
	}
	idSAT = 0;
	for (auto &r : simul->reactions)
	{
		idSAT++;
		r->idSAT = idSAT;
	}

	string inputFile = "steadyConstraints.smt2";
	string outputFile = "steadyOutput.txt";
	// string steadyFile= "SteadyStates.txt";

	string z3Command = z3path + " " + inputFile + " > " + outputFile + " 2> steadylog.txt";
	// bool printPACsToFile = Settings::getInstance()->printPACsToFile->boolValue();

	std::cout << inputFile << std::endl;  // #erase
	std::cout << outputFile << std::endl; // #erase

	stringstream clauses;

	//------ pretty printing -------
	clauses << "(set-option :pp.decimal true)\n";
	clauses << "(set-option :pp.decimal_precision 7)\n";

	//------------declare variables------------

	// concentrations of entities
	for (auto &e : simul->entities)
	{
		clauses << "(declare-const conc" << e->idSAT << " Real)\n";
	}

	// flows of reactions
	for (auto &r : simul->reactions)
	{
		clauses << "(declare-const flow" << r->idSAT << " Real)\n";
	}

	// ------------ constraints ------------
	// 1. concentrations are positive
	for (auto &e : simul->entities)
	{
		clauses << "(assert (>= conc" << e->idSAT << " 0))\n";
	}

	// 2. flows computation
	for (auto &r : simul->reactions)
	{
		clauses << "(assert (= flow" << r->idSAT << " (+";
		// assocrate
		clauses << " (* " << r->assocRate;
		for (auto &e : r->reactants)
		{
			clauses << " conc" << e->idSAT;
		}
		clauses << ")";
		// dissociate
		if (r->isReversible)
		{
			clauses << " (* -1. " << r->dissocRate;
			for (auto &e : r->products)
			{
				clauses << " conc" << e->idSAT;
			}
			clauses << ")";
		}
		else
		{
			clauses << "0";
		}
		clauses << ")))\n";
	}

	// 3. steady state
	for (auto &e : simul->entities)
	{
		clauses << "(assert (= (+";
		//reactions
		for (auto &r : simul->reactions)
		{
			int stoc = 0;
			for (auto &reac : r->reactants)
			{
				if (reac == e)
				{
					stoc--;
				}
			}
			for (auto &prod : r->products)
			{
				if (prod == e)
				{
					stoc++;
				}
			}
			if (stoc != 0)
			{
				clauses << " (* " << stoc << " flow" << r->idSAT << ")";
			}
		}
		//creation
		clauses << " " << e->creationRate;
		//destruction
		clauses << " (* -1. " << e->destructionRate << " conc" << e->idSAT<< ")";
		clauses << ") 0))\n";
	}

	stringstream modClauses; // additional clauses forbidding some models

	// int maxSteadyStates=Settings::getInstance()->maxSteadyStates->intValue();
	int maxSteadyStates = 2;
	int numStS;
	for (numStS = 0; numStS < maxSteadyStates; numStS++)
	{

		if (simul->shouldStop)
			break;

		ofstream inputStream(inputFile);
		inputStream << clauses.str();
		inputStream << modClauses.str();
		inputStream << "(check-sat)\n";
		inputStream << "(get-model)\n";

		inputStream.close();
		system(z3Command.c_str());

		ifstream outputStream(outputFile);
		if (!outputStream)
		{
			cerr << "Failed to open file: " << outputFile << endl;
			return;
		}

		string z3Output((istreambuf_iterator<char>(outputStream)),
						istreambuf_iterator<char>());

		// test if satisfiable
		size_t newlinePos = z3Output.find('\n');
		string firstLine = z3Output.substr(0, newlinePos);
		if (firstLine == "unsat")
		{
			LOG("No more steady states");
			break;
		}
		if (firstLine == "unknown")
		{
			LOGWARNING("Z3 returned unknown on SteadyStates");
			return;
		}
		if (firstLine != "sat")
		{
			LOGWARNING("Error in Z3 output");
			system("cp steadyConstraints.smt2 steadyConstraintsError.smt2");
			return;
		}

		LOG("Steady state found");

		// Parse the model
		map<string, float> model = parseModelReal(z3Output);

		// add witness to the list
		Array<float> w;
		for (auto &e : simul->entities)
		{
			w.add(model["conc" + to_string(e->idSAT)]);
		}
		steadyStates.add(w);

		// add Clause forbidding concentrations to be all epsilon close to the current ones
		float epsilon = 0.001; // to go to setting later

		modClauses << "(assert (not (and";
		int i = 0;
		for (auto &e : simul->entities)
		{
			modClauses << " (< (abs (- conc" << e->idSAT << " " << w[i] << ")) " << epsilon << ")";
			i++;
		}

		modClauses << ")))\n";
	}
	bool toPrint=true; //settings later
	if (numStS > 0)
	{

		LOG(String(numStS) + " Steady states found");

		if (toPrint)
		{
			ofstream steadyFile;
			steadyFile.open("steadyFile.txt", ofstream::out | ofstream::trunc);
			int i = 0;
			for (auto &w : steadyStates)
			{
				i++;
				steadyFile << "---Steady State " << i << " ---" << endl;
				int eid = 0;
				for (auto &c : w)
				{
					steadyFile << "ent " << eid << ": " << c << endl;
					eid++;
				}
			}
			steadyFile.close();
		}
	}
	//	simul->PACsGenerated = true;
}

/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:


vector<Polynom> SteadyStateslist::computeConcentrationRateVector()
{

	// affect id to entities in reactions
	simul->affectSATIds();

	// init rate vector
	vector<Polynom> rateVector(simul->entities.size());

	// loop over reactions
	for (auto& r: simul->reactions)
	{

		// build forward monom of current reaction
		Monom forwardRate;
		forwardRate.coef = r->assocRate;
		for (auto& reac : r->reactants)
		{
			forwardRate.variables.add(reac->idSAT);
		}

		// build backward monom of current reaction (if reversible)
		Monom backwardRate;
		if (r->isReversible)
		{
			backwardRate.coef = r->dissocRate;
			for (auto& prod : r->products)
			{
				backwardRate.variables.add(prod->idSAT);
			}
		}


		// retrieve stoechiometry vector of current reaction
		//cout << "In reaction " << r->idSAT << endl;
		map<int, int> stoec;
		for (auto& reactant : r->reactants)
		{
			stoec[reactant->idSAT]--;
		}
		for (auto& product : r->products)
		{
			stoec[product->idSAT]++;
		}


		// add forward/backward monoms for each entity involved in the reaction
		for (auto& [entID, sto] : stoec)
		{
			// entity is either consumed or produced by reaction
			Monom mon = forwardRate; 
			// multiply reaction rate by stoechiometry and add it to the rate vector
			mon.coef *= (float) sto; // multiply rate constant by stoechiometry 
			rateVector[entID].add(mon);

			// opposite if reaction is reversible  
			if (r->isReversible) 
			{
				Monom mon = backwardRate;
				// multiply reaction rate by (-stoechiometry) and add it to the rate vector 
				mon.coef *= -1. * (float) sto; // multiply rate constant by opposite stoechiometry 
				rateVector[entID].add(mon);
			}
		} // end loop over stoechiometry vector of reaction
 
	} // end reaction loop


	// // sanity check
	// int ic=-1;
	// for (auto& polynomrate : rateVector) 
	// {
	// 	ic++;
	// 	cout << "entity #" << ic << endl;
	// 	for (auto& monom : polynomrate)
	// 		{
	// 			cout << "-----------\n\tcoeff = " << monom.coef << endl;
	// 			cout << "\tvar =";
	// 			for (auto& id : monom.variables) cout << "  " << id;
	// 			cout << endl;
	// 		} 
	// 		cout << "------------" << endl;
	// } // end sanity check

	return rateVector;


} // end func computeConcentrationRateVector

/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:


// function to derivate a Polynom (arg1) wrt to variable var (arg2)
Polynom SteadyStateslist::partialDerivate(const Polynom& poly, int var)
{
  Polynom derivative;
	// loop over each monom of the polynom
  for (const auto& monom : poly) 
	{
    int count = 0; 
    for (int v : monom.variables) if (v == var) count++; // count occurence of variable var

    // if variable is there
    if (count > 0)
		{ 
      Monom derivedMonom;
      derivedMonom.coef = monom.coef * (float) count; // power of variable is absorbed in constant coef
      // Rebuild liste of variables removing one occurence of var
      bool removedOne = false;
      for (int v : monom.variables) 
			{
        if (v == var && !removedOne)
				{
          removedOne = true; // remove one occurence of var
        } 
				else 
				{
          derivedMonom.variables.add(v);
         }
      } // end loop over monom variables

      derivative.add(derivedMonom); // add monom derivative to polynome derivative
    } // end if var is present in monom to derivate
  } // end monom loop
  
	return derivative;
} // end partialDerivate

/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:

void SteadyStateslist::computeJacobiMatrix()
{
	// retrieve vector of entity rates
	vector<Polynom> rateVector = computeConcentrationRateVector();

	// set size of jacobi matrix
	//jacobiMatrix.resize(simul->entities.size(), simul->entities.size());

	// calculate jacobi matrix
	for (unsigned int i=0; i<simul->entities.size(); i++)
	{
		Array<Polynom> column;
		for (unsigned int j=0; j<simul->entities.size(); j++)
		{
			Polynom derivate = partialDerivate(rateVector[i], j);
			column.add(derivate);  // add element i,j
		}		
		// add column
		jacobiMatrix.add(column);
	}

	// sanity check
	// for (unsigned int i=0; i<simul->entities.size(); i++)
	// {
	// 	for (unsigned int j=0; j<simul->entities.size(); j++)
	// 	{
	// 		cout << "########## element (" << i << "," << j << ") ##########" << endl;
	// 		for (auto& monom : jacobiMatrix[i][j])
	// 		{
	// 			cout << "-----------\tcoeff = " << monom.coef << endl;
	// 			cout << "\tvar =";
	// 			for (auto& id : monom.variables) cout << "  " << id;
	// 			cout << endl;
	// 		} 
	// 	}
	// } // end sanity check


}

/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:



float SteadyStateslist::evaluatePolynom(Polynom poly, State witness) 
{
	float val=0.;

	for (Monom monom : poly)
	{
		float f = monom.coef;
		for (int ient : monom.variables) f *= witness[ient];
		val += f;
	}
 	return val;
}


/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:



Eigen::MatrixXd SteadyStateslist::evaluateJacobiMatrix(State& witness)
{
	Eigen::MatrixXd jm(witness.size(), witness.size());

	//cout << "witness size : " << witness.size() << endl;
	//cout << "JM size : " << jacobiMatrix.size() << endl;

	if (jacobiMatrix.size()!=witness.size()) 
	{
		LOG("Warning : formal jacobi matrix size is incorrect, can't evaluate it properly. returning incomplete evaluation.");
		return jm;
	}

	for (unsigned int i=0; i<witness.size(); i++)
	{
		if (jacobiMatrix[i].size()!=witness.size()) 
		{
			LOG("Warning : formal jacobi matrix size is incorrect, can't evaluate it properly. returning incomplete evaluation.");
			return jm;
		}
		for (unsigned int j=0; j<witness.size(); j++)
		{
			jm(i,j) = evaluatePolynom(jacobiMatrix[i][j], witness);
		}
	}

	return jm;
}

/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:


bool SteadyStateslist::isStable(Eigen::MatrixXd& jm)
{

	// init eigen solver objects for current jacobi matrix
	Eigen::EigenSolver<Eigen::MatrixXd> es(jm);

	if (es.info() == Eigen::Success) // if diagonalization succeeded
	//if (1==0)
	{
		//cout << "diagonalization succeeded" << endl;

		// retrieve eigenvalues if diagonalized
		Eigen::VectorXcd  ev =  es.eigenvalues();

		//cout << "eigenvalues are " << endl;
		//cout << ev << endl;

		bool isCertain = true;
		for (unsigned int i=0; i<ev.size(); i++) // loop over eigenvalues
		{
			if (ev[i].real() > epsilon) return false; // one positive eigenvalue implies non stability 
			if (abs(ev[i].real()) < epsilon) isCertain = false; // if -epsilon < eigenvalue < epsilon : tricky case
		}
		if (isCertain) return true;
		else
		{
			LOG("Warning, too small eigenvalue encountered, can't decide stability of stationnary point. Stability assumed !");
			return true;
		}

	} // end if diagonalization succeeded

	else // diagonalization failed
	{
		// in this case try triangularization
		// cout << "trying triangularization" << endl;

	
		Eigen::RealSchur<Eigen::MatrixXd> rs;
	  rs.compute(jm); 

		//cout << "triangular matrix : " << endl;
		//cout << rs.matrixT() << endl;

    if (rs.info() == Eigen::Success) // if triangularization succeeded
		{
			//cout << "triangularization succeeded" << endl;

			// retrieve diagonal values if diagonalized
			Array<float> diag;
			Eigen::MatrixXd tMatrix = rs.matrixT();
			for (int i=0; i<tMatrix.rows(); i++) diag.add(tMatrix(i,i));

			// sparse signs of diagonal elements
			bool isCertain = true;
			for (unsigned int i=0; i<diag.size(); i++) // loop over eigenvalues
			{
				if (diag[i] > epsilon) return false; // one positive eigenvalue implies non stability 
				if (abs(diag[i]) < epsilon) isCertain = false; // if -epsilon < eigenvalue < epsilon : tricky case
			}
			if (isCertain) return true;
			else
			{
				LOG("Warning, too small eigenvalue encountered, can't decide stability of stationnary point. Stability assumed !");
				return true;
			}
		} // end if diagonalization succeeded
	} // end non diagonalizable case

	return true; // try to habe a bit cleaner function to avoid such return default value

}



/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:



void SteadyStateslist::keepStableSteadyStatesOnly()
{

	// State mywit = {1.861, 3.839, 5.189, 7.960};
	// Array<State> testSteadyStates;
	// testSteadyStates.add(mywit);

	int nss = steadyStates.size();

	// loop over steady states
	int dynamicIndex=-1;
	for (State& witness : steadyStates)
	{
		dynamicIndex++;

		if (witness.size() != simul->entities.size()) continue; // this case occurs and bothers me

		// cout << "at steady state : (";
		// for (int k=0; k<witness.size(); k++) cout << witness[k] << ",  ";
		// cout << ")\n";

		// evaluate jacobi matrx at current state vector
		Eigen::MatrixXd jm = evaluateJacobiMatrix(witness);

		//cout << "---- Jacobi Matrix ----" << endl;
		//cout << jm << endl;

		// is steady state stable ?
		bool stable = isStable(jm);
		if (!stable)
		{
			steadyStates.remove(dynamicIndex);
			dynamicIndex--;
		}
	}

LOG("System has " + to_string(nss) + " steady states, and " + to_string(steadyStates.size()) + " are stable.");
	
}

/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:




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

