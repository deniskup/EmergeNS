#include "PAC.h"
#include "Simulation.h"
#include "Settings.h"
#include <regex>
#include <stack>
#include <cctype>

using namespace std;

float parseExpr(const string &input)
{
	string output = input;

	// Define a regular expression pattern to match expressions of the form (operator number number)
	regex pattern(R"(\(([-+*/\\]) (-?\d+\.\d+|-?[A-Za-z]+) (-?\d+\.\d+|-?[A-Za-z]+)\))");

	sregex_iterator iter(output.begin(), output.end(), pattern);
	sregex_iterator end;

	// Create a map to store variable values
	map<string, double> variables;
	int nbIter = 0;
	while (iter != end)
	{
		nbIter++;
		if (nbIter > 10)
		{
			cout << " Failed to parse expression: " << input << endl;
			return 0.0;
		}
		smatch match = *iter;

		// Extract matched components
		string fullMatch = match.str();
		char op = match[1].str()[0];
		string operand1 = match[2].str();
		// if match[3] exists
		string operand2;
		if (!match[3].matched)
		{
			// unary operator, should be "-", we do 0-operand1
			operand2 = operand1;
			operand1 = "0.";
		}
		else
		{
			operand2 = match[3].str();
		}

		// Calculate the result based on the operator and operands
		double result = 0.0;

		// Calculate the result based on the operator and numeric operands
		if (op == '+')
		{
			result = stod(operand1) + stod(operand2);
		}
		else if (op == '-')
		{
			result = stod(operand1) - stod(operand2);
		}
		else if (op == '*')
		{
			result = stod(operand1) * stod(operand2);
		}
		else if (op == '/')
		{
			result = stod(operand1) / stod(operand2);
		}
		else
		{
			cout << "Unknown operator: " << op << endl;
			return 0.;
		}

		// Convert the result to a string and replace the matched substring
		ostringstream oss;
		oss << result;
		string resultString = oss.str();
		output.replace(match.position(), match.length(), resultString);

		// Move to the next match
		++iter;
	}

	return stof(output);
}

PAC::PAC(var data, Simulation *simul)
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
				LOGWARNING("PAC construction failed: entity " + ent["ent"].toString() + " not found");
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
				LOGWARNING("PAC construction failed: reaction " + reacd["reac"].toString() + " not found");
				return;
			}
			reacDirs.add(make_pair(r, reacd["dir"]));
		}
	}
	cout << "PAC loaded: " << toString() << " with " << entities.size() << " entities and " << reacDirs.size() << " reactions" << endl;
}

var PAC::toJSONData()
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

String PAC::toString()
{
	String res;
	for (auto &rd : reacDirs)
	{
		auto r = rd.first;
		bool d = rd.second;
		// auto p = r->product;
		// auto r1 = r->reactant1;
		// auto r2 = r->reactant2;
		// String plus = "+";
		// String r1name = r1->name;
		// String r2name = r2->name;
		// if (!entities.contains(r1))
		// {
		// 	plus = "";
		// 	r1name = "";
		// }
		// if (!entities.contains(r2))
		// {
		// 	plus = "";
		// 	r2name = "";
		// }
		// if (d)
		// { // 1->2
		// 	res += r->product->name + "->" + r1name + plus + r2name + " ";
		// }
		// else
		// { // 2->1
		// 	res += r1name + plus + r2name + "->" + r->product->name + " ";
		// }
		// same but with list of reactants and products, filter by containment
		String reac = "";
		if (d)
		{ // prod->react
			for (auto &e : r->products)
			{
				if (entities.contains(e))
					reac += e->name + "+";
			}
			// remove last "+"
			reac = reac.substring(0, reac.length() - 1);
			reac += "->";
			for (auto &e : r->reactants)
			{
				if (entities.contains(e))
					reac += e->name + "+";
			}
			// remove last "+"
			reac = reac.substring(0, reac.length() - 1);
		}
		else
		{ // reacts->prod
			for (auto &e : r->reactants)
			{
				if (entities.contains(e))
					reac += e->name + "+";
			}
			// remove last "+"
			reac = reac.substring(0, reac.length() - 1);
			reac += "->";
			for (auto &e : r->products)
			{
				if (entities.contains(e))
					reac += e->name + "+";
			}
			// remove last "+"
			reac = reac.substring(0, reac.length() - 1);
		}
		res += reac + " ";
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

map<string, float> parseModelReal(const string &output)
{
	map<string, float> model;

	//  (define-fun conc2 () Real
	//(/ 3.0 4.0))
	// should return conc2 0.75

	// Regex pattern to match variable assignments
	// regex pattern(R"(define-fun ([a-zA-Z0-9_]+) \(\) Real\n\s+([0-9.]+))");
	// search for concentrations only
	regex pattern(R"(define-fun (conc[0-9_]+) \(\) Real\n\s+([^\n]+)\)\n)");

	// Iterate over matches
	sregex_iterator it(output.begin(), output.end(), pattern);
	sregex_iterator end;
	for (; it != end; ++it)
	{
		smatch match = *it;
		string varName = match.str(1);
		// cout << "varName: " << varName << " is " << match.str(2) << "\n";
		float varValue = parseExpr(match.str(2));
		// cout << varName << " " << varValue << " from " << match.str(2) << endl;
		model[varName] = varValue;
	}

	return model;
}

// add the clause for a CAC to be part of a multiCAC.
// reacsTreated is the set of reactions for which variables coef have already been declared
void addCACclause(stringstream &clauses, PAC *pac, set<SimReaction *> &reacsTreated)
{

	// compute coefs from concentrations
	for (auto &rd : pac->reacDirs)
	{
		SimReaction *r = rd.first;
		if (reacsTreated.find(r) != reacsTreated.end())
			continue;
		clauses << "(declare-const coef" << r->idSAT << " Real)\n";
		// coef is assocRate*reac1*reac2-dissocRate*prod
		// avoid printing in scientific format, print decimal values at the level of C++

		//clauses << fixed << "(assert (= coef" << r->idSAT << " (- (* " << r->assocRate << " conc" << r->reactant1->idSAT << " conc" << r->reactant2->idSAT << ") (* " << r->dissocRate << " conc" << r->product->idSAT << "))))\n";
		//use reactants and products vectors
		clauses << fixed << "(assert (= coef" << r->idSAT << " (- (* " << r->assocRate << " ";
		for (auto &e : r->reactants)
		{
			clauses << "conc" << e->idSAT << " ";
		}
		clauses << ") (* " << r->dissocRate << " ";
		for (auto &e : r->products)
		{
			clauses << "conc" << e->idSAT << " ";
		}
		clauses << "))))\n";

		reacsTreated.insert(r);
	}
	// for entities of the PAC, verify positive flow from reactions of the PAC
	for (auto &e : pac->entities)
	{
		clauses << "(assert (> (+";
		for (auto &rd : pac->reacDirs)
		{
			SimReaction *r = rd.first;
			// if (r->reactant1 == e)
			// {
			// 	clauses << " (- coef" << r->idSAT << ")";
			// }
			// if (r->reactant2 == e)
			// {
			// 	clauses << " (- coef" << r->idSAT << ")";
			// }
			// if (r->product == e)
			// {
			// 	clauses << " coef" << r->idSAT;
			// }
			for (auto er : r->reactants)
			{
				if (er == e)
				{
					clauses << " (- coef" << r->idSAT << ")";
				}
			}
			for (auto p : r->products)
			{
				if (p == e)
				{
					clauses << " coef" << r->idSAT;
				}
			}
		}
		clauses << " 0) " << Settings::getInstance()->CACRobustness->floatValue() << "))\n"; // last 0 to treat the case of no reaction, should not happen. .00001 to avoid numerical errors, and have real CAC
	}

	// acceleration option: ask that acceleration is above a threshold
	if (Settings::getInstance()->CacAccelUse->boolValue())
	{
		// declare acceleration variables for all entities and reactions not already treated
		for (auto &e : pac->entities)
		{
			clauses << "(declare-const acc" << e->idSAT << " Real)\n";
		}
		// TODO continue
	}
}

void PAClist::addCycle(PAC *newpac)
{
	// we only test if is is included in existing one, other direction is taken care of by SAT solver
	// except if Settings::nonMinimal is set to true
	bool nonMinTest = Settings::getInstance()->nonMinimalPACs->boolValue();
	bool isNonMin = false;
	for (int i = 0; i < cycles.size(); i++)
	{
		if (newpac->includedIn(cycles[i], includeOnlyWithEntities))
		{
			// cout << "PAC collision: " << newpac->toString() << " is included in " << cycles[i]->toString() << endl;
			nonMinimals.add(cycles[i]);
			cycles.remove(i);
		}
		if (nonMinTest)
		{
			if (cycles[i]->includedIn(newpac, includeOnlyWithEntities))
			{
				//	cout << "PAC collision: " << cycles[i]->toString() << " is included in " << newpac->toString() << endl;
				nonMinimals.add(newpac);
				isNonMin = true;
				break;
			}
		}
	}
	if (!isNonMin)
		cycles.add(newpac);
}

PAClist::~PAClist()
{
	stopThread(500);
}

void PAClist::printPACs()
{
	LOG("PACS computed");
	for (auto pac : cycles)
	{
		cout << pac->toString() << endl;
	}
}

void PAClist::printRACs()
{
	int nbRac = 0;
	for (auto &pac : cycles)
	{
		nbRac++;
		if (pac->wasRAC)
		{
			LOG(String(nbRac) + ": " + pac->toString());
		}
	}
}

void PAClist::clear()
{
	cycles.clear();
	nonMinimals.clear();
	CACs.clear();
	basicCACs.clear();
	simul->PACsGenerated = false;
	maxRAC = 0.;
}

void PAClist::affectSATIds()
{
	// entities
	int i = 0;
	for (auto &e : simul->entities)
	{
		e->idSAT = i;
		i++;
	}

	// reactions
	int j = 0;
	for (auto &r : simul->reactions)
	{
		r->idSAT = j;
		j++;
	}
}

// 0 for minisat, 1 for kissat, 2 for z3, 3 for CACs
void PAClist::compute(int numSolv)
{

	numSolver = numSolv;
	startThread();
}

bool PAClist::computeCAC(set<int> pacIds)
{
	// use z3 to test the existence of a witness for the CAC
	stringstream clauses;
	string inputFile = "z3CAC.smt2";
	string outputFile = "z3CACmodel.txt";
	string z3Command = z3path + " " + inputFile + " > " + outputFile + " 2> z3CAClog.txt";

	// realistic coefs: coefs come from actual concentrations of entities
	// declare concentrations variablefile:///home/thomas/Mod%C3%A8les/emergENS/EmergenceNS/ReactionSystems/z3constraints.smt2

	for (auto &e : simul->entities)
	{
		clauses << "(declare-const conc" << e->idSAT << " Real)\n";
		// bounds
		clauses << "(assert (and (>= conc" << e->idSAT << " 0) (<= conc" << e->idSAT << " 100)))\n";
	}
	set<SimReaction *> reacsTreated; // empty set of reactions already treated
	for (auto i : pacIds)
	{
		addCACclause(clauses, cycles[i], reacsTreated);
	}

	// call z3
	//  write to file
	ofstream inputStream(inputFile);
	inputStream << clauses.str();
	inputStream << "(check-sat)\n";
	inputStream << "(get-model)\n";

	inputStream.close();
	 //cout << "Calling Z3" << endl;
	system(z3Command.c_str());
	// cout << "Z3 done" << endl;
	ifstream outputStream(outputFile);
	if (!outputStream)
	{
		cerr << "Failed to open file: " << outputFile << endl;
		return false;
	}

	string z3Output((istreambuf_iterator<char>(outputStream)),
					istreambuf_iterator<char>());

	// test if satisfiable
	size_t newlinePos = z3Output.find('\n');
	string firstLine = z3Output.substr(0, newlinePos);
	if (firstLine == "unsat")
	{
		return false;
	}
	if (firstLine == "unknown")
	{
		stringstream cac;
		auto it = pacIds.begin();
		cac << *it + 1; //+1 when displaying
		it++;
		for (; it != pacIds.end(); it++)
		{
			cac << "," << *it + 1;
		}
		LOGWARNING("Z3 timeout on CAC: " + cac.str());
		return false;
	}
	if (firstLine != "sat")
	{
		LOGWARNING("Error in Z3 output");
		system("cp z3CAC.smt2 z3CACerror.smt2");
		return false;
	}
	// parse the witness of concentrations
	map<string, float> model = parseModelReal(z3Output);
	witnessType witness;
	for (auto &e : simul->entities)
	{
		witness.add(make_pair(e, model["conc" + to_string(e->idSAT)]));
	}

	CACs.add(make_pair(pacIds, witness));
	return true;
}

void PAClist::computeCACs()
{
	setZ3path();
	affectSATIds();
	// compute CACs among the PACs
	LOG("Computing CACs");
	int nbCAC = 0;
	ofstream pacFile;
	if (Settings::getInstance()->printPACsToFile->boolValue())
	{
		pacFile.open("PAC_list.txt", ofstream::out | ofstream::app);
		pacFile << endl
				<< "--- CACs ---" << endl;
	}
	CACs.clear();
	basicCACs.clear();
	const int CACsMax = Settings::getInstance()->CACSetMax->intValue();
	bool found = true;
	for (int setSize = 1; setSize <= CACsMax; setSize++)
	{
		// if(simul->shouldStop) break;
		found = false;
		// find cliques in computed sets of size SetSize-1, and test them with z3.

		set<set<int>> candidates;

		if (setSize == 1)
		{
			// put all pacs as singletons
			for (int i = 0; i < cycles.size(); i++)
			{
				set<int> singleton;
				singleton.insert(i);
				candidates.insert(singleton);
			}
		}
		else
		{
			// we only build sets that have all their subsets of size setSize-1 in the list of CACs

			for (int i = 0; i < CACs.size(); i++)
			{
				set<int> set1 = CACs[i].first;
				if (set1.size() == setSize - 1)
				{
					// we now look for another set of size setSize-1 that has intersection of size setSize-2 with set
					for (int j = i + 1; j < CACs.size(); j++)
					{
						set<int> set2 = CACs[j].first;
						if (set2.size() == setSize - 1)
						{
							vector<int> intersection;
							set_intersection(set1.begin(), set1.end(),
											 set2.begin(), set2.end(),
											 back_inserter(intersection));
							if (intersection.size() == setSize - 2)
							{
								// we have found a candidate
								set<int> candidate;
								// take it as the union of the two sets
								for (auto &e : set1)
									candidate.insert(e);
								for (auto &e : set2)
									candidate.insert(e);
								// verify that every subset of size setSize-1 is in the list of CACs
								bool ok = true;
								for (auto k : candidate)
								{
									set<int> subset;
									for (auto l : candidate)
									{
										if (l != k)
										{
											subset.insert(l);
										}
									}
									// search for subset in CACs
									ok = false;
									for (auto &c : CACs)
									{
										if (c.first == subset)
										{
											ok = true;
											break;
										}
									}
									if (!ok) // one of the subsets is already not a CAC
										break;
								}
								// add it to the list of candidates if all subsets ok
								if (ok)
									candidates.insert(candidate);
							}
						}
					}
				}
			}
		}
		if (candidates.size() == 0)
			break;
		LOG("Testing " + to_string(candidates.size()) + " candidates of size " + to_string(setSize));
		// actually test the candidates
		int localNbCAC = 0;
		for (auto &cand : candidates)
		{
			if (simul->shouldStop)
				break;
			bool res = computeCAC(cand);
			if (res)
			{
				found = true;
				nbCAC++;
				localNbCAC++;
				if (cand.size() == 1)
					basicCACs.add(*cand.begin());
				// print last cac of CACs to file
				stringstream cac;
				auto it = cand.begin();
				cac << *it + 1;
				it++;
				for (; it != cand.end(); it++)
				{
					cac << "," << *it + 1;
				}
				LOG("CAC found: " + cac.str());
				if (Settings::getInstance()->printPACsToFile->boolValue())
				{
					pacFile << cand.size() << "-CAC: ";
					for (auto &e : CACs.getLast().first)
					{
						pacFile << e << ",";
					}
					pacFile << endl;
					pacFile << "Witness: " << endl;
					for (auto &w : CACs.getLast().second)
					{
						pacFile << "\t" << w.first->name << ": " << w.second << endl;
					}
				}
			}
		}
		LOG(String(localNbCAC) + " CACs found of size " + String(setSize));
		if (!found)
			break;
	}

	if (Settings::getInstance()->printPACsToFile->boolValue())
	{
		pacFile.close();
	}
	LOG(String(nbCAC) + " CACs found");
}

void PAClist::run()
{
	// mark beginning of computation
	simul->isComputing = true;
	simul->shouldStop = false;
	// measure time
	uint32 startTime = Time::getMillisecondCounter();

	if (numSolver <= 1)
	{
		LOGWARNING("SAT Solving no longer supported, only Z3.");
		// PACsWithSAT();
	}
	else if (numSolver == 2)
	{
		PACsWithZ3();
	}
	else
		computeCACs();

	// print execution time
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
}

// Function to parse the model from Z3 output, retrieve boolean variables
map<string, bool> parseModel(const string &output)
{
	map<string, bool> model;

	// Regex pattern to match variable assignments
	regex pattern(R"(define-fun ([a-zA-Z0-9_]+) \(\) Bool\n\s+(true|false))");

	// Iterate over matches
	sregex_iterator it(output.begin(), output.end(), pattern);
	sregex_iterator end;
	for (; it != end; ++it)
	{
		smatch match = *it;
		string varName = match.str(1);
		bool varValue = (match.str(2) == "true");
		model[varName] = varValue;
	}

	return model;
}

void PAClist::setZ3path()
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
	z3path += " -t:" + to_string(Settings::getInstance()->z3timeout->intValue());
}

void PAClist::PACsWithZ3()
{
	// we implement here more directly the constraint from Blockhuis:
	// there must exist coefficients for the reactions, such that the cycle produces every of its entity

	// clear PACs if some were computed
	cycles.clear();
	nonMinimals.clear();
	CACs.clear();
	basicCACs.clear();

	LOG("Using solver: Z3");
	setZ3path();
	affectSATIds();
	string inputFile = "z3constraints.smt2";
	string outputFile = "z3model.txt";


	string z3Command = z3path + " " + inputFile + " > " + outputFile + " 2> z3log.txt";
	bool printPACsToFile = Settings::getInstance()->printPACsToFile->boolValue();

	std::cout << inputFile << std::endl; // #erase
	std::cout << outputFile << std::endl; // #erase

	stringstream clauses;
	//------------declare variables------------

	// entities
	LOG("has " + to_string(simul->entities.size()) + " entities.");
	for (auto &e : simul->entities)
	{
		clauses << "(declare-const ent" << e->idSAT << " Bool)\n";
	}

	// reactions
	LOG("has " + to_string(simul->reactions.size()) + " reactions.");
	for (auto &r : simul->reactions)
	{
		clauses << "(declare-const reac" << r->idSAT << " Bool)\n";
		clauses << "(declare-const dir" << r->idSAT << " Bool)\n";
		clauses << "(declare-const coef" << r->idSAT << " Int)\n";
	}

	//------------constraints------------

	// dir expresses the sign of coef. dir false means coef is positive A+B->AB
	for (auto &r : simul->reactions)
	{
		clauses << "(assert (= dir" << r->idSAT << " (< coef" << r->idSAT << " 0)))\n";
		if(!r->isReversible){
			clauses << "(assert (= dir" << r->idSAT << " false))\n";
		}
	}

	// each reaction has one product and one reactant true
	for (auto &r : simul->reactions)
	{
		clauses << "(assert (=> reac" << r->idSAT << " (and";
		//clauses << "(or ent" << r->reactant1->idSAT << " ent" << r->reactant2->idSAT << ")";
		clauses << "(or";
		for(auto &e : r->reactants)
		{
			clauses << " ent" << e->idSAT;
		}
		clauses << ")";
		//clauses << " ent" << r->product->idSAT;
		clauses << "(or";
		for(auto &e : r->products)
		{
			clauses << " ent" << e->idSAT;
		}
		clauses << ")";
		clauses << ")))\n";
	}

	// if distinct reactants and dir is false, then one reactant must be false
	// TODO verify with blokhuis that this is OK, and that dir is needed
	// for (auto &r : simul->reactions)
	// {
	// 	if (r->reactant1 != r->reactant2)
	// 	{

	// 		// clauses << "(assert (=> (and reac" << r->idSAT << " (not dir" << r->idSAT << ")) (or (not ent" << r->reactant1->idSAT << ") (not ent" << r->reactant2->idSAT << "))))\n";
	// 		// not care about dir here, from Blokhuis
	// 		clauses << "(assert (=> (and reac" << r->idSAT << ") (or (not ent" << r->reactant1->idSAT << ") (not ent" << r->reactant2->idSAT << "))))\n";
	// 	}
	// }

	// true reactions with coefs produce a positive amount of every true entity. Strictly positive otherwise putting everything to 0 works
	for (auto &ent : simul->entities)
	{
		clauses << "(assert (=> ent" << ent->idSAT << " (> (+";
		for (auto &r : simul->reactions)
		{
			int j = r->idSAT;
			int stoc=0;
			for(auto &e : r->reactants)
			{
				if(e==ent)
				{
					stoc--;
				}
			}
			for(auto &e : r->products)
			{
				if(e==ent)
				{
					stoc++;
				}
			}

			if (stoc!=0)
			{
				// add coefj+coefj
				clauses << " (ite reac" << j << " (* "<<stoc << " coef" << j << ") 0)";
			}
			// else if (r->reactant1 == ent || r->reactant2 == ent)
			// {
			// 	// add coefj
			// 	clauses << " (ite reac" << j << " (- coef" << j << ") 0)";
			// }
			// else if (r->product == ent)
			// {
			// 	// add -coefj
			// 	clauses << " (ite reac" << j << " coef" << j << " 0)";
			// }
			// else{
			// add 0, in case where ent does not appear in enough reactions ,and help with debugging
			//	clauses << "      0\n";
			//}
		}
		clauses << " 0) 0)))\n"; // we finally ask that this sum is strictly positive. Final 0 to treat the case of no reaction
	}

	stringstream modClauses; // additional clauses forbidding some models

	int maxSize = jmin(simul->entities.size(), simul->reactions.size(), Settings::getInstance()->maxDiameterPACs->intValue());

	for (int pacSize = 2; pacSize <= maxSize; pacSize++)
	{
		if (simul->shouldStop)
			break;
		int pacsFound = 0;
		stringstream sizeClauses;
		// pacsize entities

		sizeClauses << "(assert ((_ at-most " << pacSize << ")";
		for (auto &e : simul->entities)
		{
			sizeClauses << " ent" << e->idSAT;
		}
		sizeClauses << "))\n";

		// at -most and at-least to have the exact number of entities
		sizeClauses << "(assert ((_ at-least " << pacSize << ")";
		for (auto &e : simul->entities)
		{
			sizeClauses << " ent" << e->idSAT;
		}
		sizeClauses << "))\n";

		// exactly pacsize reactions, or just at least for non-minimal pacs

		sizeClauses << "(assert ((_ at-least " << pacSize << ")";

		for (auto &r : simul->reactions)
		{
			sizeClauses << " reac" << r->idSAT;
		}
		sizeClauses << "))\n";

		if (!Settings::getInstance()->nonMinimalPACs->boolValue())
		{
			// if only minimal, we put also at most this number of reactions
			sizeClauses << "(assert ((_ at-most " << pacSize << ")";
			for (auto &r : simul->reactions)
			{
				sizeClauses << " reac" << r->idSAT;
			}
			sizeClauses << "))\n";
		}

		while (pacsFound < Settings::getInstance()->maxPACperDiameter->intValue())
		{
			if (simul->shouldStop)
				break;
			// write to file
			ofstream inputStream(inputFile);
			inputStream << clauses.str();
			inputStream << sizeClauses.str();
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
				break;
			}
			if (firstLine == "unknown")
			{
				LOGWARNING("Z3 returned unknown on PACs");
				return;
			}
			if (firstLine != "sat")
			{
				LOGWARNING("Error in Z3 output");
				system("cp z3constraints.smt2 z3constrainserror.smt2");
				return;
			}

			pacsFound++;

			// Parse the model
			map<string, bool> model = parseModel(z3Output);

			PAC *pac = new PAC();
			for (auto &r : simul->reactions)
			{
				int j = r->idSAT;
				if (model["reac" + to_string(j)])
				{
					pac->reacDirs.add(make_pair(r, model["dir" + to_string(j)]));
				}
			}
			for (auto &e : simul->entities)
			{
				int i = e->idSAT;
				if (model["ent" + to_string(i)])
				{
					pac->entities.add(e);
				}
			}

			addCycle(pac);

			// add Clause forbidding PACs containing  this one

			modClauses << "(assert (not (and";
			for (auto &r : pac->reacDirs)
			{
				int j = r.first->idSAT;
				modClauses << " reac" << j;
				if (r.second)
					modClauses << " dir" << j;
				else
					modClauses << " (not dir" << j << ")";
			}
			for (auto &e : pac->entities)
			{
				int i = e->idSAT;
				modClauses << " ent" << i;
			}

			if (Settings::getInstance()->nonMinimalPACs->boolValue())
			{
				// add clause forbidding this exact PAC, for and reactions not in the PAC
				// suffices to ask no extra reactions
				for (auto &r : simul->reactions)
				{
					if (pac->reacDirs.contains(make_pair(r, false)) || pac->reacDirs.contains(make_pair(r, true)))
						continue;
					int j = r->idSAT;
					modClauses << " (not reac" << j << ")";
				}
			}

			modClauses << ")))\n";
		}
		if (pacsFound > 0)
			LOG(String(pacsFound) + " PACs" + " of size " + String(pacSize));
	}
	if (printPACsToFile)
	{
		ofstream pacFile;
		pacFile.open("PAC_list.txt", ofstream::out | ofstream::trunc);
		pacFile << "--- Minimal PACs ---" << endl;
		for (auto &pac : cycles)
			pacFile << pac->toString() << endl;
		if (Settings::getInstance()->nonMinimalPACs->boolValue())
		{
			pacFile << endl
					<< "--- Non-minimal PACs ---" << endl;
			for (auto &pac : nonMinimals)
				pacFile << pac->toString() << endl;
		}
		pacFile << endl;
		pacFile.close();
	}
	simul->PACsGenerated = true;

	//computeCACs();


}

String PAClist::CACToString(CACType cac)
{

	stringstream ss;
	auto it = cac.first.begin();
	ss << *it + 1; //+1 when displaying
	it++;
	for (; it != cac.first.end(); it++)
	{
		ss << "," << *it + 1;
	}
	return String(ss.str());
}

CACType PAClist::dummyCAC()
{
	set<int> emptyset;
	CACType dumCAC = make_pair(emptyset, witnessType());
	return dumCAC;
}

CACType PAClist::CACfromInt(int i)
{

	if (i < 1 || i > CACs.size())
	{
		LOGWARNING("CACfromInt: CAC index out of bounds:" + to_string(i));
		return dummyCAC();
	}
	int j = 1;
	for (auto &cac : CACs)
	{
		if (i == j)
			return cac;
		j++;
	}
	LOGWARNING("CACfromInt: CAC not found:" + to_string(i));
	return dummyCAC();
}

var PAClist::CACtoJSON(CACType cac)
{
	var data = new DynamicObject();
	var pacids;
	int i = 0;
	for (auto &p : cac.first)
	{
		var pacid = new DynamicObject();
		pacid.getDynamicObject()->setProperty("id", p);
		pacids.append(pacid);
		i++;
	}
	data.getDynamicObject()->setProperty("pacids", pacids);
	// witnessType is Array<pair<SimEntity *,float>>
	var witness;
	for (auto &w : cac.second)
	{
		var wdata = new DynamicObject();
		wdata.getDynamicObject()->setProperty("entity", w.first->name);
		wdata.getDynamicObject()->setProperty("value", w.second);
		witness.append(wdata);
	}
	data.getDynamicObject()->setProperty("witness", witness);

	return data;
}

CACType PAClist::JSONtoCAC(var data)
{
	set<int> pacids;

	// test pacids exists and is an array
	if (!data.hasProperty("pacids") || !data["pacids"].isArray())
	{
		LOGWARNING("PAClist::JSONtoCAC: pacids not found or not an array");
		return dummyCAC();
	}
	Array<var> *pacidsData = data["pacids"].getArray();
	for (auto &p : *pacidsData)
	{
		pacids.insert(p["id"]);
	}
	if (!data.hasProperty("witness") || !data["witness"].isArray())
	{
		LOGWARNING("PAClist::JSONtoCAC: witness not found or not an array");
		return dummyCAC();
	}
	Array<var> *witnessData = data["witness"].getArray();
	witnessType witness;
	for (auto &w : *witnessData)
	{
		witness.add(make_pair(simul->getSimEntityForName(w["entity"]), w["value"]));
	}
	return make_pair(pacids, witness);
}

var PAClist::toJSONData()
{
	var data = new DynamicObject();
	// save cycles
	var cyclesData;
	for (auto &c : cycles)
	{
		cyclesData.append(c->toJSONData());
	}
	data.getDynamicObject()->setProperty("cycles", cyclesData);
	// save CACs
	var CACsData;
	for (auto &c : CACs)
	{
		CACsData.append(CACtoJSON(c));
	}
	data.getDynamicObject()->setProperty("CACs", CACsData);
	return data;
}

void PAClist::fromJSONData(var data)
{
	clear();
	// load cycles
	if (!data.getDynamicObject()->hasProperty("cycles") || !data["cycles"].isArray())
	{
		LOGWARNING("wrong PAC format in PAClist JSON data");
		return;
	}
	Array<var> *cyclesData = data["cycles"].getArray();
	for (auto &c : *cyclesData)
	{
		PAC *pac = new PAC(c, simul);
		cycles.add(pac);
	}
	simul->PACsGenerated = true;
	// load CACs
	if (!data.getDynamicObject()->hasProperty("CACs") || !data["CACs"].isArray())
	{
		LOGWARNING("Wrong CAC format in PAClist JSON data");
		return;
	}
	Array<var> *CACsData = data["CACs"].getArray();
	for (auto &c : *CACsData)
	{
		CACType cac = JSONtoCAC(c);
		CACs.add(cac);
		if (cac.first.size() == 1)
			basicCACs.add(*(cac.first.begin()));
	}
}
