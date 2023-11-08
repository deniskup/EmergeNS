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

	while (iter != end)
	{
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
		}else{
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
				return;
			}
			reacDirs.add(make_pair(r, reacd["dir"]));
		}
	}
	// cout << "PAC loaded: " << toString() << " with " << entities.size() << " entities and " << reacDirs.size() << " reactions" << endl;
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

map<string, float> parseModelReal(const string &output)
{
	map<string, float> model;

	//  (define-fun conc2 () Real
	//(/ 3.0 4.0))
	// should return conc2 0.75

	// Regex pattern to match variable assignments
	// regex pattern(R"(define-fun ([a-zA-Z0-9_]+) \(\) Real\n\s+([0-9.]+))");
	//search for concentrations only
	regex pattern(R"(define-fun (conc[0-9_]+) \(\) Real\n\s+([^\n]+)\)\n)");

	// Iterate over matches
	sregex_iterator it(output.begin(), output.end(), pattern);
	sregex_iterator end;
	for (; it != end; ++it)
	{
		smatch match = *it;
		string varName = match.str(1);
		//cout << "varName: " << varName << " is " << match.str(2) << "\n";
		float varValue = parseExpr(match.str(2));
		//cout << varName << " " << varValue << " from " << match.str(2) << endl;
		model[varName] = varValue;
	}

	return model;
}

void PAC::computeCAC(Simulation *simul)
{
	// use z3 to test the existence of a witness for the CAC
	stringstream clauses;
	string inputFile = "z3CAC.smt2";
	string outputFile = "z3CACmodel.txt";
	string z3Command = "z3 " + inputFile + " > " + outputFile + " 2> z3CAClog.txt";

	// realistic coefs: coefs come from actual concentrations of entities
	// declare concentrations variable
	for (auto &e : simul->entities)
	{
		clauses << "(declare-const conc" << e->idSAT << " Real)\n";
		// bounds
		clauses << "(assert (and (>= conc" << e->idSAT << " 0) (<= conc" << e->idSAT << " 100)))\n";
	}
	// compute coefs from concentrations
	for (auto &rd : reacDirs)
	{
		SimReaction *r = rd.first;
		clauses << "(declare-const coef" << r->idSAT << " Real)\n";
		// coef is assocRate*reac1*reac2-dissocRate*prod
		clauses << "(assert (= coef" << r->idSAT << " (- (* " << r->assocRate << " conc" << r->reactant1->idSAT << " conc" << r->reactant2->idSAT << ") (* " << r->dissocRate << " conc" << r->product->idSAT << "))))\n";
	}
	// for entities of the PAC, verify positive flow from reactions of the PAC
	for (auto &e : entities)
	{
		clauses << "(assert (> (+";
		for (auto &rd : reacDirs)
		{
			SimReaction *r = rd.first;
			if (r->reactant1 == e)
			{
				clauses << " (- coef" << r->idSAT << ")";
			}
			if (r->reactant2 == e)
			{
				clauses << " (- coef" << r->idSAT << ")";
			}
			if (r->product == e)
			{
				clauses << " coef" << r->idSAT;
			}
		}
		clauses << " 0) 0.00001))\n"; // last 0 to treat the case of no reaction, should not happen. .00001 to avoid numerical errors, and have real CAC
	}
	// call z3
	//  write to file
	ofstream inputStream(inputFile);
	inputStream << clauses.str();
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
		isCAC = false;
		return;
	}
	if (firstLine != "sat")
	{
		LOGWARNING("Error in Z3 output");
		return;
	}
	isCAC = true;
	// parse the witness of concentrations
	map<string, float> model = parseModelReal(z3Output);
	for (auto &e : simul->entities)
	{
		witness.add(make_pair(e, model["conc" + to_string(e->idSAT)]));
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
	simul->PACsGenerated = false;
	maxRAC = 0.;
}

void cleanKissatOutput()
{
	ifstream infile("model.txt");
	ofstream outfile("model2.txt");
	string line;
	while (getline(infile, line))
	{
		if (line[0] == 'v' || line[0] == 's')
		{
			line.erase(0, 2);
			outfile << line << endl;
		}
		else
		{
			cout << "Error in Kissat output" << endl;
			break;
		}
	}
	infile.close();
	outfile.close();
	system("mv model2.txt model.txt");
}

// 0 for minisat, 1 for kissat
void PAClist::computePACs(int numSolv)
{

	numSolver = numSolv;
	startThread();
}

void PAClist::computeCACS()
{
	// compute CACs among the PACs
	LOG("Computing CACs");
	int nbCAC = 0;
	ofstream pacFile;
	if(Settings::getInstance()->printPACsToFile->boolValue()){
		pacFile.open("PAC_list.txt", ofstream::out | ofstream::app);
		pacFile << endl
				<< "--- CACs ---" << endl;
	}
	for (auto &pac : cycles)
	{
		pac->computeCAC(simul);
		if (pac->isCAC)
		{
			nbCAC++;
			if(Settings::getInstance()->printPACsToFile->boolValue()){
				
				pacFile << pac->toString() << endl;
				pacFile << "Witness: "<<endl;
				for (auto &w : pac->witness)
				{
					pacFile << "\t"<<w.first->name << ": " << w.second << endl;
				}
			}
		}
	}
	if(Settings::getInstance()->printPACsToFile->boolValue()){
		pacFile.close();
	}
	LOG(String(nbCAC) + " CACs found");
	
}

void PAClist::run()
{ // clear PACs if some were computed
	cycles.clear();
	nonMinimals.clear();
	// measure time
	uint32 startTime = Time::getMillisecondCounter();

	if (numSolver <= 1)
		PACsWithSAT();
	else
		PACsWithZ3();

	// print execution time
	LOG("Execution time: " << String(Time::getMillisecondCounter() - startTime) << " ms");
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

void PAClist::PACsWithZ3()
{
	// we implement here more directly the constraint from Blockhuis:
	// there must exist coefficients for the reactions, such that the cycle produces every of its entity

	LOG("Using solver: Z3");
	string inputFile = "z3constraints.smt2";
	string outputFile = "z3model.txt";
	string z3Command = "z3 " + inputFile + " > " + outputFile + " 2> z3log.txt";

	bool printPACsToFile = Settings::getInstance()->printPACsToFile->boolValue();

	stringstream clauses;
	//------------declare variables------------

	// entities
	int i = 0;
	for (auto &e : simul->entities)
	{
		e->idSAT = i;
		clauses << "(declare-const ent" << i << " Bool)\n";
		i++;
	}

	// reactions
	int j = 0;
	for (auto &r : simul->reactions)
	{
		r->idSAT = j;
		clauses << "(declare-const reac" << j << " Bool)\n";
		clauses << "(declare-const dir" << j << " Bool)\n";
		clauses << "(declare-const coef" << j << " Real)\n";
		j++;
	}

	//------------constraints------------

	// dir expresses the sign of coef. dir false means coef is positive A+B->AB
	for (auto &r : simul->reactions)
	{
		clauses << "(assert (= dir" << r->idSAT << " (< coef" << r->idSAT << " 0)))\n";
	}

	// each reaction has its product and one reactant true
	for (auto &r : simul->reactions)
	{
		clauses << "(assert (=> reac" << r->idSAT << " (and";
		clauses << "(or ent" << r->reactant1->idSAT << " ent" << r->reactant2->idSAT << ")";
		clauses << " ent" << r->product->idSAT;
		clauses << ")))\n";
	}

	// if distinct reactants and dir is false, then one reactant must be false
	for (auto &r : simul->reactions)
	{
		if (r->reactant1 != r->reactant2)
		{
			clauses << "(assert (=> (and reac" << r->idSAT << " (not dir" << r->idSAT << ")) (or (not ent" << r->reactant1->idSAT << ") (not ent" << r->reactant2->idSAT << "))))\n";
		}
	}

	// true reactions with coefs produce a positive amount of every true entity. Strictly positive otherwise putting everything to 0 works
	for (auto &ent : simul->entities)
	{
		clauses << "(assert (=> ent" << ent->idSAT << " (> (+";
		for (auto &r : simul->reactions)
		{
			int j = r->idSAT;
			if (r->reactant1 == ent && r->reactant2 == ent)
			{
				// add coefj+coefj
				clauses << " (ite reac" << j << " (+ (- coef" << j << ") (- coef" << j << ")) 0)";
			}
			else if (r->reactant1 == ent || r->reactant2 == ent)
			{
				// add coefj
				clauses << " (ite reac" << j << " (- coef" << j << ") 0)";
			}
			else if (r->product == ent)
			{
				// add -coefj
				clauses << " (ite reac" << j << " coef" << j << " 0)";
			}
			// else{
			// add 0, in case where ent does not appear in enough reactions ,and help with debugging
			//	clauses << "      0\n";
			//}
		}
		clauses << " 0) 0)))\n"; // we finally ask that this sum is strictly positive. Final 0 to treat the case of no reaction
	}

	stringstream modClauses; // additional clauses forbidding some models

	int maxSize = jmin(simul->entities.size(), simul->reactions.size(), Settings::getInstance()->maxDiameterPACs->intValue());

	for (int pacSize = 3; pacSize <= maxSize; pacSize++)
	{
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
			if (firstLine != "sat")
			{
				LOGWARNING("Error in Z3 output");
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

	computeCACS();

	simul->PACsGenerated = true;
	simul->updateParams();
}

void PAClist::PACsWithSAT()
{
	bool debugMode = false; // to print the file of vars for SAT

	Settings *settings = Settings::getInstance();

	// declare SAT solvers
	String kissatCommand = settings->pathToKissat->stringValue() + " -q dimacs.txt > model.txt";
	SATSolver minisat("minisat", "minisat dimacs.txt model.txt >SATlog.txt", "SAT", false);
	SATSolver kissat("kissat", kissatCommand, "SATISFIABLE", true);

	Array<SATSolver *> solvers = {&minisat, &kissat};

	SATSolver *solver = solvers[numSolver];

	LOG("Using solver: " + solver->name);

	// compute return values of the solver on Sat and Non-Sat input

	// create satisfiable dimacs
	ofstream dimacs;
	dimacs.open("dimacs.txt", ofstream::out | ofstream::trunc);
	dimacs << "p cnf 1 1" << endl;
	dimacs << "1 0" << endl;
	dimacs.close();
	const int satReturnValue = system(solver->command.getCharPointer());
	if (solver->printsExtraString)
		cleanKissatOutput();
	ifstream sol_file("model.txt");
	string testSat;

	sol_file >> testSat;

	if (testSat != solver->satLine)
	{
		LOGWARNING("Positive test of SAT Solver failed, exiting");
		return;
	}

	sol_file.close();

	dimacs.open("dimacs.txt", ofstream::out | ofstream::trunc);
	dimacs << "p cnf 1 2" << endl;
	dimacs << "1 0" << endl;
	dimacs << "-1 0" << endl;
	dimacs.close();

	const int unsatReturnValue = system(solver->command.getCharPointer());

	// verify that model.txt contains the right output
	if (solver->printsExtraString)
		cleanKissatOutput();
	sol_file.open("model.txt");

	sol_file >> testSat;

	if (testSat == solver->satLine)
	{
		LOGWARNING("Negative test of SAT Solver failed, exiting");
		return;
	}

	sol_file.close();

	stringstream clauses;

	ofstream varfile;
	if (debugMode)
		varfile.open("vars.txt", ofstream::out | ofstream::trunc);

	ofstream pacFile;
	if (settings->printPACsToFile->boolValue()) // todo implement
		pacFile.open("PAC_list.txt", ofstream::out | ofstream::trunc);
	//  for now to Dimacs, to integrate with Kissat later

	// a PAC is a subset of n reactions and n entities, such that
	//  -every entity is reactant of exactly one of the reactions, and product of at least one
	//  -there is an entity produced twice
	int nbClauses = 0;

	int Nent = simul->entities.size();
	int Nreac = simul->reactions.size();

	int curvar = 0; // number of current variable
	// if entity i is taken in the cycle C
	Array<int> ent;
	ent.resize(Nent);
	int ei = 0, j; // , k;
	for (auto &e : simul->entities)
	{
		curvar++;
		ent.set(ei, curvar);
		if (debugMode)
			varfile << "Ent " << e->name << ": " << curvar << endl;
		e->idSAT = ei;
		ei++;
	}

	// if reaction j is taken in the cycle C
	Array<int> reac;
	reac.resize(Nreac);
	// for taken reactions: which direction is used. 0 is reactants->product and 1 is product->reactants
	Array<int> dir;
	dir.resize(Nreac);

	Array<int> doubleProds; // doubleProds[j] is the variable for "both products of reaction j are in the PAC"
	doubleProds.resize(Nreac);
	Array<int> doubleReac; // doubleReac[j] is the variable for "reaction j is in the PAC and has a double reactant"

	j = 0;
	for (auto &r : simul->reactions)
	{
		curvar++;
		reac.set(j, curvar);
		if (debugMode)
			varfile << "Reac " << r->reactant1->name << "+" << r->reactant2->name << " : " << curvar << endl;
		r->idSAT = j;
		curvar++;
		dir.set(j, curvar);
		if (debugMode)
			varfile << "Dir " << curvar << endl;
		curvar++;
		doubleProds.set(j, curvar);
		if (debugMode)
			varfile << "DoubleProds " << curvar << endl;
		curvar++;
		doubleReac.set(j, curvar);
		if (debugMode)
			varfile << "DoubleReac " << curvar << endl;
		j++;
	}

	// TODO optimize: only put the variables that have a chance to be true, ie isReac[c2(i,j)] exists only if entity i appears in reaction j.
	//  use Hashtables instead of double/triple arrays

	// compress 2 indices (Nent,Nreac) into one
	auto c2 = [&](int a, int b)
	{
		return a * Nreac + b;
	};
	// compress 3 indices (Nent,Nreac,Nreac) into one
	// auto c3 = [&](int a, int b, int c)
	// {
	// 	return a * Nreac * Nreac + b * Nreac + c;
	// };

	// add only possible ones
	unordered_map<int, int> isReac; // isReac[c2(i,j)] is the variable for "entity i is reactant of reaction j"
	unordered_map<int, int> isProd; // isProd[c2(i,j)] is the variable for "entity i is product of reaction j"
	for (auto &r : simul->reactions)
	{
		int idr = r->idSAT;
		// ids of entities involved
		int id1 = r->reactant1->idSAT;
		int id2 = r->reactant2->idSAT;
		int id3 = r->product->idSAT;
		Array<int> ids = {id1, id2, id3};

		// possibility of double product
		// if (id1 == id2)
		// {
		// 	curvar++;
		// 	isProds[c3(id1, idr, idr)] = curvar;
		// 	varfile << "is2Prods " << r->reactant1->name << " : " << curvar << endl;
		// }
		for (auto i : ids)
		{
			curvar++;
			isReac[c2(i, idr)] = curvar;
			if (debugMode)
				varfile << "isReac " << i << " in " << r->name << " : " << curvar << endl;
			curvar++;
			isProd[c2(i, idr)] = curvar;
			if (debugMode)
				varfile << "isProd " << r->reactant1->name << " from " << r->name << " : " << curvar << endl;
			//  for (auto &r2 : simul->reactions)
			//  {
			//  	if (r2->idSAT <= idr)
			//  		continue;
			//  	if (i == r2->reactant1->idSAT || i == r2->reactant2->idSAT || i == r2->product->idSAT)
			//  	{

			// 		curvar++;
			// 		isProds[c3(i, idr, r2->idSAT)] = curvar;
			// 		//if(debugMode)  varfile << "isProds " << ent[i] << " from " << r->reactant1->name << "+" << r->reactant2->name << " and " << r2->reactant1->name << "+" << r2->reactant2->name << " : " << curvar << endl;
			// 	}
			// }
		}
	}

	// local function to add clause:
	auto addClause = [&](Array<int> disjuncts)
	{
		for (int d : disjuncts)
		{
			clauses << d << " ";
		}
		clauses << "0" << endl;
		nbClauses++;
	};

	// correctness of isReac: either e is a reactant and dir=0, or e is a product and dir=1. Also reac[j] has to be true
	// for isReac to be true we also need to verify that the other reactant is different, we do not want to allow A+A->AA in this direction

	for (auto &r : simul->reactions)
	{
		j = r->idSAT;

		// isReac true implies reac chosen, and isProds c3(i,l,s) entity exists
		//  not isReac[c2(i,j)] OR reac[j]
		int id1 = r->reactant1->idSAT;
		int id2 = r->reactant2->idSAT;
		int id3 = r->product->idSAT;
		Array<int> ids = {id1, id2, id3};
		Array<int> idleft = {id1, id2};

		if (id1 == id2)
		{

			// doubleProds[j] <=> dir[j] and reac[j] and ent[i]
			addClause({doubleProds[j], -dir[j], -reac[j], -ent[id1]});
			addClause({-doubleProds[j], ent[id1]});
			addClause({-doubleProds[j], dir[j]});
			addClause({-doubleProds[j], reac[j]});

			// doubleReac <=> -dir and reac and ent[i]
			addClause({doubleReac[j], dir[j], -reac[j], -ent[id1]});
			addClause({-doubleReac[j], reac[j]});
			addClause({-doubleReac[j], -dir[j]});
			addClause({-doubleReac[j], ent[id1]});

			int ij = c2(id1, j);

			// isProd <=> dir and reac
			addClause({-isProd[ij], reac[j]});
			addClause({-isProd[ij], dir[j]});
			addClause({isProd[ij], -dir[j], -reac[j]});

			// isReac <=> -dir and reac
			addClause({-isReac[ij], reac[j]});
			addClause({-isReac[ij], -dir[j]});
			addClause({isReac[ij], dir[j], -reac[j]});
		}
		else
		{ // if different, we can put conditions on both isReac
			for (auto i : idleft)
			{
				int ij = c2(i, j);
				// isProd <=> dir and reac
				addClause({-isProd[ij], reac[j]});
				addClause({-isProd[ij], dir[j]});
				addClause({isProd[ij], -dir[j], -reac[j]});

				// isReac <=> -dir and reac
				addClause({-isReac[ij], reac[j]});
				addClause({-isReac[ij], -dir[j]});
				addClause({isReac[ij], dir[j], -reac[j]});
			}
			// compute doubleProds
			// doubleProds[j] <=> dir and ent[id1] and ent[id2] and reac[j]
			addClause({-doubleProds[j], ent[id1]});
			addClause({-doubleProds[j], ent[id2]});
			addClause({-doubleProds[j], dir[j]});
			addClause({-doubleProds[j], reac[j]});
			addClause({doubleProds[j], -ent[id1], -ent[id2], -dir[j], -reac[j]});

			// doubleReac false
			addClause({-doubleReac[j]});
		}
		// for the solitary side
		//  isReac <=> dir and reac
		int ij = c2(id3, j);
		addClause({-isReac[ij], reac[j]});
		addClause({-isReac[ij], dir[j]});
		addClause({isReac[ij], -dir[j], -reac[j]});
		// isProd <=> -dir and reac
		addClause({-isProd[ij], reac[j]});
		addClause({-isProd[ij], -dir[j]});
		addClause({isProd[ij], dir[j], -reac[j]});
	}

	// each entity appears at least once as reactant and as product
	for (int i = 0; i < Nent; i++)
	{
		// e not chosen or appears as reactant of r
		// not ent[i] or OR_j isReac[c2(i,j)]

		// todo optimize with less loops, find is not needed

		clauses << -ent[i];
		for (j = 0; j < Nreac; j++)
		{
			auto it = isReac.find(c2(i, j));
			if (it != isReac.end())
				clauses << " " << it->second;
		}
		clauses << " 0" << endl;
		nbClauses++;
		// not ent[i] or OR_j isProd[c2(i,j)]
		clauses << -ent[i];
		for (j = 0; j < Nreac; j++)
		{
			auto it = isProd.find(c2(i, j));
			if (it != isProd.end())
				clauses << " " << it->second;
		}
		clauses << " 0" << endl;
		nbClauses++;
		// an entity appears as reactant in at most one reaction
		// AND_{j<k} not ent[i] or not isReac[c2(i,j)] or not isReac[c2(i,k)]

		// todo optimize, and understand why not redundant

		for (j = 0; j < Nreac; j++)
		{
			auto it1 = isReac.find(c2(i, j));
			if (it1 == isReac.end())
				continue;
			for (int k = j + 1; k < Nreac; k++)
			{

				auto it2 = isReac.find(c2(i, k));
				if (it2 == isReac.end())
					continue;

				addClause({-ent[i], -it1->second, -it2->second});
			}
		}
	}
	// if the reaction is two to one (dir=0), and the two reactants differ, they can't be both in the PAC:
	//  AND_j -reac[j] or dir[j] or not ent[reac1] or not ent[reac2]
	for (auto &r : simul->reactions)
	{
		if (r->reactant1 == r->reactant2)
			continue;
		j = r->idSAT;
		addClause({-reac[j], dir[j], -ent[r->reactant1->idSAT], -ent[r->reactant2->idSAT]});
	}
	// in each selected reaction, at least one reactant and the product are selected
	for (auto &r : simul->reactions)
	{
		j = r->idSAT;
		addClause({-reac[j], ent[r->reactant1->idSAT], ent[r->reactant2->idSAT]});
		addClause({-reac[j], ent[r->product->idSAT]});
	}

	// one entity is produced twice
	// OR_i OR_{j<=k} isProds[c3(i,j,k)]

	// at least one DoubleProds, now in extraClauses

	// for (int j = 0; j < Nreac; j++)
	// {
	// 	clauses << doubleProds[j] << " ";
	// }
	// clauses << "0" << endl;
	// nbClauses++;

	// number of variables (and var max) without connexity
	const int nbVarBase = curvar;

	int nbAddedReacClauses = 0;
	string addedReacClauses = "";
	int nbAddedReacVars = 0;

	// write the dimacs, adding connexity with maximal distance to produce the autocatalyst, in order to find solutions in increasing size

	// don't forget that clauses will grow with models.
	auto addReacClauses = [&](int nbDoubleReac)
	{
		int nbTotVar = nbVarBase; // restart curvar from beginning of connexity
		nbAddedReacClauses = 0;
		nbAddedReacVars = 0;

		// extra clauses: connexity with dmax, doubleReacs
		stringstream extraClauses;
		// local function to add clause:
		auto addExtraClause = [&](Array<int> disjuncts)
		{
			for (int di : disjuncts)
			{
				extraClauses << di << " ";
			}
			extraClauses << "0" << endl;
			nbAddedReacClauses++;
		};

		// clauses dealing with reactions A+A->B

		// at most nbDoubleReac number of doubleReac
		function<void(int, int, Array<int> &)> loopReac = [&](int remain, int currentReac, Array<int> &currentClause) -> void
		{
			if (remain == 0)
			{
				addExtraClause(currentClause);
				return;
			}
			if (currentReac >= Nreac)
				return;
			loopReac(remain, currentReac + 1, currentClause); // we do not put currentReac in the list
			currentClause.add(-doubleReac[currentReac]);
			loopReac(remain - 1, currentReac + 1, currentClause); // we put currentReac in the list
			currentClause.removeLast();
		};
		Array<int> currentClause;
		loopReac(nbDoubleReac + 1, 0, currentClause); // the +1 comes from the fact that we forbid nb+1 doubleReac true

		// at least nbDoubleReac+1 number of doubleProds
		// for this we create a variable isKthDoubleProd[j][k] which is true if reaction  is the kth doubleProd

		unordered_map<int, int> isKthDoubleProd;

		auto e2 = [&](int j, int k)
		{ return j * (nbDoubleReac + 1) + k; };

		for (int j = 0; j < Nreac; j++)
		{
			for (int k = 0; k < nbDoubleReac + 1; k++)
			{
				nbTotVar++;
				isKthDoubleProd[e2(j, k)] = nbTotVar;
				if (debugMode)
					varfile << "isKthDoubleProd[" << j << "][" << k << "]=" << nbTotVar << endl;
			}
		}

		for (auto &r : simul->reactions)
		{
			int j = r->idSAT;
			for (int k = 0; k < nbDoubleReac + 1; k++)
			{
				// isKthDoubleProd[j][k] => doubleProds[j]
				addExtraClause({-isKthDoubleProd[e2(j, k)], doubleProds[j]});
				// iskthdoubleProd[j][k]=> for all k'<k, exists j'<j iskthdoubleprod[j'][k']
				for (int k2 = 0; k2 < k; k2++)

				{
					Array<int> smallerKclause;
					smallerKclause.add(-isKthDoubleProd[e2(j, k)]); // left side of implication
					for (int j2 = 0; j2 < j; j2++)
					{
						smallerKclause.add(isKthDoubleProd[e2(j2, k2)]); // disjunct in right side of implication
					}
					addExtraClause(smallerKclause);
				}
			}
		}

		// finally we want at least nbDoubleReac+1 doubleProds, so there is a isKthDoubleProd[j][nbReac] true
		Array<int> atLeastNclause;
		for (int j = 0; j < Nreac; j++)
		{
			atLeastNclause.add(isKthDoubleProd[e2(j, nbDoubleReac)]);
		}
		addExtraClause(atLeastNclause);

		addedReacClauses = extraClauses.str();
		nbAddedReacVars = nbTotVar - nbVarBase;
	};

	auto writeDimacs = [&](int distMax)
	{
		int nbTotVar = nbVarBase + nbAddedReacVars;
		int nbTotClauses = nbClauses + nbAddedReacClauses;

		// extra clauses: connexity with dmax, doubleReacs
		stringstream extraClauses;
		// local function to add clause:
		auto addExtraClause = [&](Array<int> disjuncts)
		{
			for (int di : disjuncts)
			{
				extraClauses << di << " ";
			}
			extraClauses << "0" << endl;
			nbTotClauses++;
		};

		// add variables for connexity: dist[e,i,f] means that entity e produces entity f in at most i steps.

		// this is a naive encoding in Ent^2, we can do Ent*log(Ent)+Reac with bit encoding of distance
		Array<int> dist;
		dist.resize(Nent * (distMax + 1) * Nent);

		auto d2 = [&](int a, int b, int c)
		{
			return a * (distMax + 1) * Nent + b * Nent + c;
		};

		for (auto &e : simul->entities)
		{
			for (auto &f : simul->entities)
			{
				for (int d = 0; d <= distMax; d++)
				{
					nbTotVar++;
					dist.set(d2(e->idSAT, d, f->idSAT), nbTotVar);
				}
			}
		}

		// diameter/connexity clauses
		for (int i = 0; i < Nent; i++)
		{

			for (j = 0; j < Nent; j++)
			{
				// 0 distance true iff i=j
				if (i == j)
					addExtraClause({dist[d2(i, 0, i)], -ent[i]});
				else
					addExtraClause({-dist[d2(i, 0, j)], -ent[i], -ent[j]});

				for (int d = 0; d <= distMax; d++)
				{
					// dist=>ent
					addExtraClause({-dist[d2(i, d, j)], ent[i]});
					addExtraClause({-dist[d2(i, d, j)], ent[j]});
				}
			}
		}
		// advance(f,r,d,t)=isProd(f,r) and dist(f,d,t)
		// d<distMax is enough here since it is an advancement to d from d+1
		unordered_map<int, int> advance;
		auto d3 = [&](int a, int b, int c, int t)
		{
			return a * Nreac * distMax * Nent + b * distMax * Nent + c * Nent + t;
		};
		// initialisation
		for (auto &r : simul->reactions)
		{
			for (int d = 0; d < distMax; d++)
			{
				for (int t = 0; t < Nent; t++)
				{
					nbTotVar++;
					advance[d3(r->reactant1->idSAT, r->idSAT, d, t)] = nbTotVar;
					nbTotVar++;
					advance[d3(r->reactant2->idSAT, r->idSAT, d, t)] = nbTotVar;
					nbTotVar++;
					advance[d3(r->product->idSAT, r->idSAT, d, t)] = nbTotVar;
				}
			}
		}

		// variables for counting doubleReacs vs forks.
		// unordered_map<int, int> doubleReacs;

		// clauses advance
		for (auto &r : simul->reactions)
		{
			int id1 = r->reactant1->idSAT;
			int id2 = r->reactant2->idSAT;
			int id3 = r->product->idSAT;
			Array<int> ids = {id1, id2, id3};

			int idr = r->idSAT;
			for (auto &f : ids)
			{

				for (int d = 0; d < distMax; d++)
				{
					for (int t = 0; t < Nent; t++)
					{
						// advance(f,r,d)=isProd(f,r) and dist(f,d)
						addExtraClause({-advance[d3(f, idr, d, t)], isProd[c2(f, idr)]});
						addExtraClause({-advance[d3(f, idr, d, t)], dist[d2(f, d, t)]});
						addExtraClause({advance[d3(f, idr, d, t)], -isProd[c2(f, idr)], -dist[d2(f, d, t)]});
					}
				}
			}
		}

		// dist(e,d+1)=> dist(e,d) OR_(e->f) advance(f,r,d)
		for (int t = 0; t < Nent; t++)
		{
			for (int d = 0; d < distMax; d++)
			{
				for (auto &e : simul->entities)
				{

					Array<int> distClause;
					distClause.add(-dist[d2(e->idSAT, d + 1, t)]);
					distClause.add(dist[d2(e->idSAT, d, t)]);
					for (auto &r : simul->reactions)
					{
						int idr = r->idSAT;
						if (!r->contains(e))
							continue;
						if (e == r->product)
						{
							distClause.add(advance[d3(r->reactant1->idSAT, idr, d, t)]);
							distClause.add(advance[d3(r->reactant2->idSAT, idr, d, t)]);
							continue;
						}
						// only remaining case: e is a reactant of r
						distClause.add(advance[d3(r->product->idSAT, idr, d, t)]);
					}
					addExtraClause(distClause);
				}
			}
		}
		// finally, every chosen entity must satisfy distMax to every other
		for (int i = 0; i < Nent; i++)
		{
			for (int t = 0; t < Nent; t++)
			{
				addExtraClause({-ent[i], -ent[t], dist[d2(i, distMax, t)]});
			}
		}
		// write the dimacs
		ofstream dimacsStream;
		dimacsStream.open("dimacs.txt", ofstream::out | ofstream::trunc);
		dimacsStream << "p cnf " << nbTotVar << " " << nbTotClauses << endl;
		dimacsStream << clauses.str();
		dimacsStream << addedReacClauses;
		dimacsStream << extraClauses.str();

		// cout << "Dimacs generated with " << Nent << " entities and " << Nreac << " reactions\n";
		// cout << curvar << " variables and " << nbClauses << " clauses\n";
		dimacsStream.close();
	};

	// load settings

	int dmax_stop = settings->maxDiameterPACs->intValue(); // maximal diameter
	dmax_stop = jmin(dmax_stop, Nent);					   // put to Nent if bigger

	int doubleReacMax = settings->maxDoubleReacPACs->intValue(); // maximal number of double reactions

	const int maxCycles = settings->maxPACperDiameter->intValue(); // max number of cycles of some level before timeout

	for (int nbDoubleReac = 0; nbDoubleReac <= doubleReacMax; nbDoubleReac++)
	{
		LOG("Generating PACs with " + String(nbDoubleReac) + " double reactions");
		// TODO continue

		addReacClauses(nbDoubleReac);

		for (int dmax = 1; dmax < dmax_stop; dmax++)
		{
			writeDimacs(dmax);
			// bool sat = true;

			int nCycles;
			for (nCycles = 0; nCycles < maxCycles; nCycles++)
			{

				int retVal = system(solver->command.getCharPointer());
				if (retVal != satReturnValue && retVal != unsatReturnValue)
				{
					LOGWARNING("SAT Solver command failed, exiting...");
					LOGWARNING("Command: " + solver->command);
					return;
				}
				if (solver->printsExtraString)

					cleanKissatOutput();

				ifstream sol_file("model.txt");
				string isSat;

				sol_file >> isSat;

				if (isSat != solver->satLine)
					break;

				int d;
				PAC *pac = new PAC();
				Array<int> newClause;
				// build new clause: one of the entity or reaction must be not used (otherwise we would have inclusion)
				// we can still find smaller one with same dmax, in which case the first one found will be removed
				for (auto &e : simul->entities)
				{
					sol_file >> d;
					if (d > 0)
					{
						newClause.add(-d);
						pac->entities.add(e);
					}
				}
				for (auto &r : simul->reactions)
				{
					// reaction
					int re, dp;
					sol_file >> re;
					// pop direction
					sol_file >> d;
					// pop double prods
					sol_file >> dp;
					// pop double reac
					sol_file >> dp;
					if (re > 0)
					{
						if (!includeOnlyWithEntities)
						{
							newClause.add(-re);
							newClause.add(-d);
						}
						pac->reacDirs.add(make_pair(r, (d > 0)));
					}
				}
				addCycle(pac);

				if (settings->printPACsToFile->boolValue())
					pacFile << pac->toString() << endl;

				if (debugMode)
				{
					if (pac->entities.size() != pac->reacDirs.size())
					{
						LOGWARNING("Problem with PAC :" << pac->toString());
						LOGWARNING("Entities: " << pac->entities.size() << " reactions: " << pac->reacDirs.size());
						LOGWARNING("Exiting...");
						return;
					}

					bool doubleReacfound = false;
					for (auto &rd : pac->reacDirs)
					{
						if (rd.second == false) // wrong direction for double product
							continue;
						if (pac->entities.contains(rd.first->reactant1) && pac->entities.contains(rd.first->reactant2))
						{
							doubleReacfound = true;
							break;
						}
					}
					if (!doubleReacfound)
					{
						LOGWARNING("No double product in PAC :" << pac->toString());
						LOGWARNING("Exiting...");
						return;
					}
				}

				addClause(newClause);
				writeDimacs(dmax);
			}
			if (nCycles > 0)
				LOG(nCycles << " PACs found for diameter=" << dmax);
			// else
			// 	cout << ".";
			if (nCycles == maxCycles)
			{
				LOGWARNING(to_string(maxCycles) + " PACs reached for diameter " + to_string(dmax) + ", stop looking");
				break;
			}
		}
	} // end loop on nbDoubleReac
	cout << endl;

	if (debugMode)
		varfile.close();
	if (settings->printPACsToFile->boolValue())
		pacFile.close();

	simul->PACsGenerated = true;

	simul->updateParams();
	// simul->printPACs();
}
