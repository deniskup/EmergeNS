#include "SteadyStates.h"

//#include <Eigen/Eigenvalues> 
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

// Function to check if a character is an operator
bool isOperator(char c) {
    return (c == '+' || c == '-' || c == '*' || c == '/');
}

// Fonction to perform arithmetic operation between two operands
long double applyOperation(long double a, long double b, char op)
{
  switch (op) {
    case '+':
      return (a + b);
    case '-':
      return (a - b);
    case '*':
      return (a * b);
    case '/':
      if (b != 0) return (a / b);
      else throw juce::OSCFormatError("Division par zéro !");  
    case '^':
      return pow(a, b);
    default:
      throw juce::OSCFormatError("Opérateur invalide !");
    }
    return 0.;
}



// Function to evaluate formal expression
// input argument : string containing operations to perform, such as :
// "1 + 3*2 - 2^4/6"
// can handle operators '+', '-', '*', '/', '^' and their relative priority 
// can't handle stuff such as brackets
// spaces do not matter, function will ignore them.
long double evaluate_expression(const string& expr)
{
  // remove all spaces from input expression which can trigger unexpected behaviors
  string expression = expr;
	while (expression.find_first_of(" ") != expression.npos) expression.erase(expression.find_first_of(" "), 1);
  

  // case where string to evaluate starts with '+' or '-' will be pathological
  // --> add operand '0.' at the beginning of the string
  if (expression[0] == '-' || expression[0] == '+') expression = "0." + expression;


  stack<long double> operandStack;
  stack<char> operatorStack;
  
  for (size_t i = 0; i < expression.length(); ++i)
  {
    if (expression[i] == ' ') continue; // Ignore spaces, already taken into account but you never know
    
    //cout << expression[i] << endl;
    
    if (isdigit(expression[i])) // first case : character is a digit
    {
    //cout << "--> is a digit" << endl;
      // Extract complete operand of expression
      string operandStr;
      while (i < expression.length() && (isdigit(expression[i]) || expression[i]=='.' )) 
      {
        operandStr += expression[i];
        i++;
      }
      i--;

      // convert current chain into a long double and put it in the operand stack
      operandStack.push(stold(operandStr));
      //cout << "\tadded operand " << operandStr << " converted to " << stold(operandStr) << endl;
    } 
     
    // if encountering a power operation, perform it straight away
    else if (expression[i]=='^')
    {  
    	//cout << "power operator ! " << endl;
    	char op = expression[i];
    
    	long double operand1 = operandStack.top();
    	operandStack.pop();
    
    	// operand2 should be next operand, extract it
    	i++;
    	string operandStr;
    	while (i < expression.length() && (isdigit(expression[i]) || expression[i]=='.' )) 
    	{
      	operandStr += expression[i];
      	i++;
    	}
    	i--;
    	long double operand2 = stold(operandStr);
      
    	operandStack.push(applyOperation(operand1, operand2, op));

    //cout << "op --> " << operand1 << " " << op << " " << operand2 << " = " << applyOperation(operand1, operand2, op) << endl;
    
    }


    // 3rd case : when encountering an operator different than '^', perform calculation respecting priority rules
    else if (isOperator(expression[i])) 
    {
    //cout << "is operator" << endl;

			// perform all previous '*' and '/' operations if current expression is '+' or '-'
      while (!operatorStack.empty() && 
             isOperator(operatorStack.top()) && 
             ((expression[i] != '*' && expression[i] != '/') || 
             (operatorStack.top() == '*' || operatorStack.top() == '/'))) 
      {
       	char op = operatorStack.top();
       	operatorStack.pop();

       	long double operand2 = operandStack.top();
       	operandStack.pop();

       	long double operand1 = operandStack.top();
       	operandStack.pop();

       	operandStack.push(applyOperation(operand1, operand2, op));

	//cout << "op --> " << operand1 << " " << op << " " << operand2 << " = " << applyOperation(operand1, operand2, op) << endl;

    	}

      // Add current operator to stack operators
      operatorStack.push(expression[i]);
    } 

		else 
		{
			string bad = {expression[i]};
      LOG("Warning : non-valid caracter in expression, return 0. ! Bad wharacter is : '" + bad + "'");
			return 0.;
    }

  } // end for loop over characters of string expression
  
    //cout << "performing remaining operations" << endl; 

    // Perform remaining operations
    while (!operatorStack.empty()) 
		{
      char op = operatorStack.top();
      operatorStack.pop();

      long double operand2 = operandStack.top();
      operandStack.pop();

      long double operand1 = operandStack.top();
      operandStack.pop();

      operandStack.push(applyOperation(operand1, operand2, op));

			//cout << "op --> " << operand1 << " " << op << " " << operand2 << " = " << applyOperation(operand1, operand2, op) << endl;
    }

    // operand stack eventually contains result of operations
		//cout << expression << " = " << operandStack.top() << endl;
    if (!operandStack.empty()) return operandStack.top();
    else 
		{
			LOG("Warning : Problem when evaluating string expression, returning 0");
			return 0.;
		}
} // end func




///////////////////////////////////////////////////////////
///////////////// SteadyStatelist METHODS /////////////////
///////////////////////////////////////////////////////////

SteadyStateslist::~SteadyStateslist()
{
	stopThread(500);
}


void SteadyStateslist::printOneSteadyState(State& s)
{
	ostringstream out;
	out.precision(3);
	out << fixed << "(";
  for (auto& c : s) out << c << ", ";
	out << ")";
	LOG(out.str());
}


////////////////////////////////////////////////////:


void SteadyStateslist::printSteadyStates()
{
	for (auto& s: steadyStates)
	{
		printOneSteadyState(s);
	}
}


////////////////////////////////////////////////////:

void SteadyStateslist::clear()
{
	steadyStates.clear();
	stableStates.clear();
	partiallyStableStates.clear();
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


	//computeWithZ3(); // search for stationnary points
	computeWithMSolve(); // search for stationnary points


	// print z3/msolve execution time
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



	// evaluate stability of stationnary points

	computeJacobiMatrix(); // formally calculate jacobi matrix of chemical reaction network

	evaluateSteadyStatesStability();

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
clear();

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

	// decimal printing of floats
	//clauses << fixed << setprecision(10);

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
		clauses << fixed << setprecision(5) << " (* " << r->assocRate;
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
	int maxSteadyStates = 4;
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

		// print steady states
		LOG("1 Steady state found..."); 
	

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

		LOG(String(numStS) + " Steady states found with Z3. List:");	
		printSteadyStates();

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

// find most inner list elements between [...] of msolve outputs and returns them as a string list
vector<string> extract_msolve_intervals(const string& chain)
{
  vector<string> result;
  size_t pos = 0;

  while (pos != string::npos) 
	{
    size_t start = chain.find_first_of('[', pos);
    size_t end = chain.find_first_of(']', start);
		// first '[' might not be the most inner one. Loop back from closing bracket to retrieve most inner ']'
    for (int k=end; k>=0; k--)
     {
      if (chain[k]=='[') 
      {
  	    start = k;
   		  break;
      }
    }

  	// store inner list      
  	if (start != string::npos && end != string::npos) 
		{
    	string element = chain.substr(start + 1, end - start - 1);
    	result.push_back(element);
    	pos = end + 1;
    } 
		else 
			{
        break;
      }
  }

    return result;
}

/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:


// input string interval has the form "A, B"
// where A and B can contain arithmetic operations
long double evaluate_interval_center(string str_interval)
{

	int separator = str_interval.find(',');
	if (separator == str_interval.npos) 
	{	
		LOG("problem in root solution interval, comma missing. return 0.");
		return 0.;
	}
	string sinf = "";
	string ssup = "";

	for (int k=0; k<separator; k++) sinf += str_interval[k];
	for (int k=separator+1; k<str_interval.size(); k++) ssup += str_interval[k];


	long double inf = evaluate_expression(sinf);
	long double sup = evaluate_expression(ssup);

	long double center = (inf + sup) / 2.;

	//cout << sinf << "\t" << ssup << endl;
	//cout << "center = " << center << endl;
	
	return center;
}

/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:





void SteadyStateslist::setMSolvepath()
{
	if (msolvepath != "") // already has been done
		return;
	
	msolvepath = Settings::getInstance()->pathToMSolve->stringValue().toStdString();
	
}


/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:



void SteadyStateslist::computeWithMSolve()
{
clear();

cout << "setting msolve path" << endl;
	// compute steady states
	setMSolvepath();
	//msolvepath = "/home/thomas/Modèles/msolve-0.6.5/msolve";


	LOG("Computing steady states with msolve...");
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

	string inputFile = "msolveSteadyConstraints.ms";
	string outputFile = "msolveSteadyOutput.ms";
	// string steadyFile= "SteadyStates.txt";

	string msolveCommand = msolvepath + " -p 32 " +  " -f " + inputFile + " -o " + outputFile + " > msolvesteadylog.txt";

	//std::cout << inputFile << std::endl;  // #erase
	//std::cout << outputFile << std::endl; // #erase

	vector<Polynom> rateVector = computeConcentrationRateVector();


	// clauses for msolve
	stringstream clauses;

	// first line of clause file contains variable names
	string line = "";
	for (int i=0; i<simul->entities.size(); i++) 
	{
		if (i == (simul->entities.size()-1)) line += "c" + to_string(i) + "\n";
		else line += "c" + to_string(i) + ", ";
	}
	clauses << line;

	// add a 0 on second line
	clauses << "0\n";

	// set digit precision for polynoms writing
	int ndigits = 4;
	double factor = pow(10, ndigits);
	clauses << fixed << setprecision(ndigits);

	// transpose rate vector into as many (string) polynoms for msolve
	int count=-1;
	for (auto& poly : rateVector)
	{
		count++;
		bool isFirst = true;
		for (auto& mono : poly)
		{
			double coef = mono.coef * factor;
			//double integercoef = mono.coef;
			long int integercoef = round(coef); 
			if (isFirst)
			{
				clauses << integercoef;
				isFirst = false;
			}
			else
			{
				string sign = (integercoef < 0) ? "-" : "+";
				clauses << " " << sign << " " << abs(integercoef);
			}
			for (auto& v : mono.variables) 
			{
				int pow = v.second;
				if (pow > 1)
				{	
					clauses << "*c" << v.first << "^" << pow;
				}
				else 
				{
					clauses << "*c" << v.first;
				}
			}
		}
	if (count<(rateVector.size()-1)) clauses << ",\n";
	}

	// write clauses into txt file
 	ofstream inputStream(inputFile);
	inputStream << clauses.str();
	inputStream.close();



	// launch msolve command
	system(msolveCommand.c_str());

	// retrieve output result
	ifstream outputStream(outputFile);
	if (!outputStream)
	{
		cerr << "Failed to open file: " << outputFile << endl;
		return;
	}

	string msolveOutput((istreambuf_iterator<char>(outputStream)),
					istreambuf_iterator<char>());

	//cout << "MSolve out ?" << endl;
	//cout << msolveOutput << endl;

	// check if a finite number of solutions were found
	int mark1 = msolveOutput.find_first_of("[");
	int mark2 = msolveOutput.find_first_of(",");
	string dim = "";
	for (int k=mark1+1; k<mark2; k++) dim += msolveOutput.at(k);
	//cout << "MSolve dim ? --> " << dim << endl;

	// only treat the case where dim = 0 : there exist a finite number of steady states
	if (dim != "0")
	{
		LOG("non finite number of steady state, either none or infinite. Exiting");
		return;
	}

	// Retrieve lists of steady state intervals from msolve output

	// extract all root intervals
	vector<string> list = extract_msolve_intervals(msolveOutput);
	// for (auto& element : list)
	// {
	// 	cout << element << endl;
	// }
	// make sure number of msolve roots is a multiple of Nentities 
	int nsol = list.size() / simul->entities.size();
	if ((list.size() % simul->entities.size()) != 0)
	{
		LOG("total number of concentration solutions isn't a multiple of Nentities. Exiting");
		return;
	}

	// convert intervals to long double
	// and store according to the number of solutions
	for (int i=0; i<nsol; i++)
	{
		// vector of increasing index
		vector<int> l(simul->entities.size(), 0);
		iota(l.begin(), l.end(), i*simul->entities.size());
		
		State state;
		bool keepState = true;
		for (auto& index : l)
		{
			long double centerLd = evaluate_interval_center(list[index]);
			float center = (float) centerLd; // move to float precision
			if (center>=0)
			{
				state.add( (float) centerLd);
			}
			else
			{
				keepState = false;
				break;
			}
		}
		if (keepState) 
		{
			if (state.size() != simul->entities.size())
			{
				LOG("steady state size different from Nentities. State not kept.");
			}
			else
			{
				steadyStates.add(state);
			}
		}
	}

	// print result
	string sStr="";
	if (steadyStates.size()>1) sStr = 's';
	LOG(" msolve found " + to_string(steadyStates.size()) + " steady state" + sStr);

	// sanity check
	//printSteadyStates();

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

		if (!r->enabled) continue;

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

		
		// build forward and backward monom of current reaction
		Monom forwardRate, backwardRate;
		forwardRate.coef = r->assocRate;
		backwardRate.coef = r->dissocRate;
		//for (auto& reac : r->reactants)
		for (auto& [id, st] : stoec)
		{
			//forwardRate.variables.add(reac->idSAT);
			if (st<0) // entity 'c_id' is a product, add "c_id^st" to monom 
			{
				forwardRate.variables.add(make_pair(id, abs(st)));
			}
			if (st>0 /*&& r->isReversible*/) // can possibly avoid useless effort if reaction is irreversible. I keep it for symmetric reasons
			{
				backwardRate.variables.add(make_pair(id, st));
			}
		}



		// add forward/backward monoms for each entity involved in the reaction
		for (auto& [entID, sto] : stoec) // entity is either consumed or produced by reaction. Information carried by sign of stoechiometry
		{
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

	// // add creation and destruction rates for each entity
	for (int ir=0; ir<rateVector.size(); ir++)
	{

		//cout << "entity #" << ir << " : " << simul->entities[ir]->name << endl;
		//cout << "kc = " << simul->entities[ir]->creationRate << "\tkd = " << simul->entities[ir]->destructionRate << endl;
		// creation rate
		if (simul->entities[ir]->creationRate > 0 && simul->entities[ir]->primary)
		{
			Monom creat;
			creat.coef = simul->entities[ir]->creationRate;
			rateVector[ir].add(creat);
		}

		if (simul->entities[ir]->destructionRate > 0)
		{
			Monom dest;
			dest.coef = -1. * simul->entities[ir]->destructionRate;
			dest.variables.add(make_pair(ir, 1)); // destruction rate has the form -kd*c_i
			rateVector[ir].add(dest);
		}
	}


	// // sanity check
	// int ic=-1;
	// for (auto& polynomrate : rateVector) 
	// {
	// 	ic++;
	// 	cout << "entity #" << ic << endl;
	// 	for (auto& monom : polynomrate)
	// 		{
	// 			cout << "-----------\n\tcoeff = " << monom.coef << endl;
	// 			cout << "\tvars =";
	// 			for (auto& p : monom.variables) cout << "c" << p.first << "^" << p.second << "  ";
	// 			cout << endl;
	// 		} 
	// 		cout << "------------" << endl;
	// } // end sanity check


	// factorize monoms with same variables together
	vector<Polynom> factRateVector(simul->entities.size());
	int irv=-1;
	for (auto& poly : rateVector)
	{
		irv++;
		Array<int> match;
		for (int i=0; i<poly.size(); i++)
		{
			if (match.contains(i)) continue;
			map<int, int> m1;
			for (auto& p : poly[i].variables) m1[p.first] = p.second;
			for (int j=i+1; j<poly.size(); j++)
			{
				map<int, int> m2;
				for (auto& p : poly[j].variables) m2[p.first] = p.second;
				if (m1==m2)
				{
					match.add(j);
					poly.getReference(i).coef += poly[j].coef;
				}
			} // end internal loop over monoms
		} // end first loop on monoms
		Polynom factPoly;
		for (int i=0; i<poly.size(); i++)
		{
			if (match.contains(i)) continue;
			factPoly.add(poly[i]);
		}
	factRateVector[irv] = factPoly;
	} // end rate Vector loop



	// sanity check
	// cout << "\n\n----- Sanity check on factorization -------" << endl;
	// int ic2=-1;
	// for (auto& polynomrate : factRateVector) 
	// {
	// 	ic2++;
	// 	cout << "entity #" << ic2 << endl;
	// 	for (auto& monom : polynomrate)
	// 		{
	// 			cout << "-----------\n\tcoeff = " << monom.coef << endl;
	// 			cout << "\tvars =";
	// 			for (auto& p : monom.variables) cout << "c" << p.first << "^" << p.second << "  ";
	// 			cout << endl;
	// 		} 
	// 		cout << "------------" << endl;
	// } // end sanity check



	return factRateVector;


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
    //for (int v : monom.variables) if (v == var) count++; // count occurence of variable var
    for (pair p : monom.variables)
		{
			int v = p.first;
			int pow = p.second;
			if (v == var) count = pow; // count occurence of variable var
		}

    // if input argument variable is in the monom
    if (count > 0)
		{ 
      Monom derivedMonom;
      derivedMonom.coef = monom.coef * (float) count; // power of variable is absorbed in constant coef
      // Rebuild liste of variables removing one occurence of var
      // bool removedOne = false;
      // for (int v : monom.variables) 
			// {
      //   if (v == var && !removedOne)
			// 	{
      //     removedOne = true; // remove one occurence of var
      //   } 
			// 	else 
			// 	{
      //     derivedMonom.variables.add(v);
      //   }
	    for (pair p : monom.variables)
			{
				int v = p.first;
				int pow = p.second;
				if (v==var) 
				{
					if (pow>1) // only add strictly positive powers of current variable
					{
						derivedMonom.variables.add(make_pair(v, pow-1));
					}
				}
				else // leave untouched variable not equal to input var argument
				{
					derivedMonom.variables.add(make_pair(v, pow));
				}
			}
      derivative.add(derivedMonom); // add monom derivative to polynome derivative
		}
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
	jacobiMatrix.clear();
	//jacobiMatrix.resize(simul->entities.size(), simul->entities.size());

	// calculate jacobi matrix
	for (unsigned int i=0; i<simul->entities.size(); i++)
	{
		Array<Polynom> line;
		for (unsigned int j=0; j<simul->entities.size(); j++)
		{
			Polynom derivate = partialDerivate(rateVector[i], j);
			//jacobiMatrix[i][j] = derivate;
			line.add(derivate);  // add element i,j
		}		
		// add column
		jacobiMatrix.add(line);
	}

	// sanity check 
	// cout << "---- Jacobi Matrix ----" << endl;
	// for (unsigned int i=0; i<simul->entities.size(); i++)
	// {
	// 	for (unsigned int j=0; j<simul->entities.size(); j++)
	// 	{
	// 		cout << "########## element (" << i << "," << j << ") ##########" << endl;
	// 		for (auto& monom : jacobiMatrix[i][j])
	// 		{
	// 			cout << "-----------\tcoeff = " << monom.coef << endl;
	// 			cout << "\tvar =";
	// 			for (auto& p : monom.variables) cout << " c" << p.first << "^" << p.second;
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
		for (pair p : monom.variables) 
		{
			int ient = p.first;
			int pow = p.second;
			for (int k=0; k<pow; k++) f *= witness[ient];
		}
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

	//cout << "witness size : " << witness.size() << "\t";
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
			cout << "witness size : " << witness.size() << "\t";
			cout << "JM column size : " << jacobiMatrix[i].size() << endl;
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


bool SteadyStateslist::isStable(Eigen::MatrixXd& jm, State& witness)
{

	// as a general info, commands to diagonalize a matrix are :
	// //init eigen solver objects for current jacobi matrix
	// Eigen::EigenSolver<Eigen::MatrixXd> es(jm);
	// if (es.info() == Eigen::Success) // if diagonalization succeeded
	// {
				// retrieve eigenvalues :
				//cout << es.eigenvalues() << endl;
				//cout << es.eigenvectors() << endl;
	// 	// retrieve eigenvalues if diagonalized
		//}

		// jacobi matrix should be always triangularizable on C
		// so I directly reach this option without bothering on diagonalization
		Eigen::ComplexSchur<Eigen::MatrixXd> cs;
	  cs.compute(jm); 

		// just in case it failed, print a warning
		if (cs.info() != Eigen::Success)
		{
			LOG("Warning : complex schur decomposition of jacobi matrix failed. Can't decide on stability, returning true by default");
			return true;
		}

		// retrieve upper triangular matrix
		Eigen::MatrixXcd triang = cs.matrixT();

		cout << "--------triang. of jacobi matrix---------" << endl;
		cout << triang << endl;

		// sparse signs of real part of diagonal elements
		bool isCertain = true;
		for (unsigned int i=0; i<triang.rows(); i++) // loop over eigenvalues
		{
			if (triang(i,i).real() > epsilon) return false; // one positive eigenvalue implies non stability 
			if (abs(triang(i,i).real()) <= epsilon)  isCertain = false; // if 0 < eigenvalue < epsilon : tricky case
		}
		if (isCertain) // no diagonal element too close from 0 and all negative
		{
			return true;
		} 
		else
		{
			if (jm.rows() < jacobiMatrix.size())
			{
				LOG("WARNING, can't decide partial stability of stationnary point (assumed true) :");
			}
			else
			{
				LOG("WARNING, can't decide global stability of stationnary point (assumed true) :");
			}
			printOneSteadyState(witness);
			// ostringstream out;
			// out.precision(3);
			// out << fixed << "(";
  		// for (auto& c : witness) out << c << ", ";
			// out << ")";
			// LOG(out.str());
			return true;
		}
	

	return true; // try to habe a bit cleaner function to avoid such return default value

}



/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:

bool SteadyStateslist::isPartiallyStable(Eigen::MatrixXd& jm, State& witness)
{
	// retrieve index where witness elements are 0
	Array<int> zeroindex;
	for (int k=0; k<witness.size(); k++)
	{
		if (witness.getReference(k)==0.) zeroindex.add(k);
	}

	// Init sub jacobi matrix
	int subsize = witness.size() - zeroindex.size();
	Eigen::MatrixXd subjm(subsize, subsize);

	// Retrieve elements of global jacobi matrix associated to non-zero witness element
	Array<float> eljm;
	for (int i=0; i<witness.size(); i++)
	{
		if (zeroindex.contains(i)) continue;
		for (int j=0; j<witness.size(); j++)
		{
			if (zeroindex.contains(j)) continue;
			eljm.add(jm(i,j));
		}
	}

	// sanity check on sizes
	if (eljm.size() != (subsize*subsize))
	{
		LOG("Warning, size issue with partial Jacobi Matrix");
		LOG("partial stability can't be trusted for steady state:");
		printOneSteadyState(witness);
	}

	// Fill sub jacobi matrix
	for (int i=0; i<subsize; i++)
	{
		for (int j=0; j<subsize; j++)
		{
			int index = j + i*subsize;
			subjm(i,j) = eljm.getReference(index);
		}
	}

cout << "----- Sub Jacobi Matrix-----" << endl;
cout << subjm << endl;

// build sub witness state
State subWitness;
for (int k=0; k<witness.size();k++)
{
	if (!zeroindex.contains(k)) subWitness.add(witness.getReference(k));
}

bool stable = isStable(subjm, witness);



return stable;

}



/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:
/////////////////////////////////////////////////////////////////////////:


void SteadyStateslist::evaluateSteadyStatesStability()
{

	int nss = steadyStates.size();	// keep track of how many steady states there are

	// loop over steady states
	for (int iw=steadyStates.size()-1; iw>=0; iw--)
	{
		State witness = steadyStates.getReference(iw);

		cout << "evaluating steady state : (";
		for (int k=0; k<witness.size(); k++) cout << witness[k] << ",  ";
		cout << ")\n";

		if (witness.size() != simul->entities.size()) // just in case
		{
			steadyStates.remove(iw);
			continue; 
		}
		
		// evaluate jacobi matrx at current state vector
		Eigen::MatrixXd jm = evaluateJacobiMatrix(witness);

		//cout << "---- Jacobi Matrix ----" << endl;
		//cout << jm << endl;

		// is steady state globally stable ?
		bool stable = isStable(jm, witness);
		if (stable) stableStates.add(witness);

		// if (stable) cout << "--> stable !" << endl;
		// else cout << "--> unstable !" << endl;

		// steady state contains 0. elements ?
		bool shouldGoPartial = witness.contains(0.);
		// if yes, check partial stability
		if (shouldGoPartial)
		{
			bool partiallyStable = isPartiallyStable(jm, witness);
			if (partiallyStable) partiallyStableStates.add(witness);
			// if (partiallyStable) cout << "--> partially stable !" << endl;
			// else cout << "--> partially unstable !" << endl;
		}
	}

// print stable steady states 
string plural = (stableStates.size()>1) ? "s" : "";
LOG("System has " + to_string(stableStates.size()) + " stable steady state" + plural + " : ");
for (auto& s: stableStates) printOneSteadyState(s);

// print partially stable steady states
plural = (partiallyStableStates.size()>1) ? "s" : "";
LOG("System has " + to_string(partiallyStableStates.size()) + " partially stable steady state" + plural + " : ");
for (auto& s: partiallyStableStates) printOneSteadyState(s);
	
} // end func evaluateSteadyStatesStability

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

	// save steady states
	// var steadystateListData;
	// for (auto &s : steadyStates)
	// {
	// 	var state = new DynamicObject();
	// 	state.getDynamicObject()->setProperty("state", s);


	// 	steadystateListData.append(state);
	// }
	// data.getDynamicObject()->setProperty("steadyStates!!", steadystateListData);


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

