#include "SteadyStates.h"
#include "Simulation.h"
#include "Settings.h"
#include <regex>
#include <stack>
#include <cctype>
#include "PAC.h" //for ParseModel

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


	computeWithZ3();

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




void SteadyStateslist::defaultJacobiMatrix(int size)
{

// init Jacobi Matrix with 0 only
	string strzero = "0.";
	for (int i=0; i<size; i++)
	{
		Array<string> zeroline;
		for (int j=0; j<size; j++) zeroline.add("0.");
		strJacobiMatrix.add(zeroline);
	}

	// for (auto& line : strJacobiMatrix)
	// {
	// 	for (auto& el : line) cout << el << "  ";
	// 	cout << endl; 
	// }

}




// input term should be of the form "k0*ci*...*cj + k1*ci*...*cj"
string SteadyStateslist::PartialDerivate(string term, string var)
{

  ///cout << "input term (to derivate wrt to " << var <<  ") : " << term << endl;
  
  std::string partial = "";

  // get ready for the while loop
  std::stringstream sterm(term);
  std::string subterm = "";

  while(getline(sterm, subterm, '#')) // separate each term of the input string 
  {
		///cout << "\t\tsubterm " << subterm << endl;
		if (subterm.find(var)==subterm.npos) 
		{
			///cout << "\tno dependence on " << var << endl;
			partial += "+0."; // remove case where derivate = 0 straight away
			///cout << "\t\tpow = 0" << endl;
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

		///cout << "\t\tpower equals " << pow << endl;
    
    // init partial derivate of current subterm
  	string subpartial = subterm + "*" + to_string(pow) + ".";

		// reduce power of var by 1, by chanchin var into a '1'
		subpartial.replace(subpartial.find(var.c_str()), var.size(), "1.");

   
  	// remove subsequent double products
  	while (subpartial.find("**")!=subpartial.npos) subpartial.replace(subpartial.find("**"), 2, "*");
  
  	// remove first character and last characters if equal to '*'
  	//if (subpartial.at(0)=='*') subpartial.erase(0, 1);
  	//if (subpartial[subpartial.size()-1]=='*') subpartial.erase(subpartial.size()-1, 1);

  	// add subpartial to total partial derivative
  	partial += subpartial;
  	///cout << "\t\t" << subpartial << endl;
  
}

// clean last character
if (partial[partial.size()-1]=='+') partial.erase(partial.size()-1, 1);

///cout << "output term : " << partial << endl << endl;

return partial;

} 




void SteadyStateslist::computeJacobiMatrix()
{

	// affect id to entities in reactions
	simul->affectSATIds();

	// Init a vector<string> of size #entites
	vector<string> dcdt(simul->entities.size());

	// init jacobi matrix with "0." only
	defaultJacobiMatrix(simul->entities.size());

	//cout << "simu  has " << simul->entities.size() << " entites" << endl;


	for (auto& r : simul->reactions)
	{
		// retrieve stoechiometry vector of current reaction
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


		// build string rate factor associated to current forward reaction
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

		// add forward or backward terms to time derivate of concentrations
		//bool isFirst=true;
		string sep="#";
		for (auto& [id, st] : stoec)
		{
			if (st<0) // reactant case
			{
				dcdt[id] += sep + to_string(st) + ".*" + fac_forward;
				if (r->isReversible) dcdt[id] += sep + "+" + to_string(abs(st)) + "*" + fac_backward;
			}
			if (st>0) // product case
			{
				dcdt[id] += sep + "+" + to_string(st) + ".*" + fac_forward;
				if (r->isReversible) dcdt[id] += sep + to_string(-st) + "*" + fac_backward;
			}
			// if (isFirst)
			// 	{
			// 		isFirst=false;
			// 		sep="#";
			// 	}
		}
	} // end reaction loop

	// remove first character '#'
	for (auto& der : dcdt)
	{
		if (der[0]=='#') der.erase(0, 1);
		//cout << der << endl;
	}


	// // fill Jacobi Matrix with its formal expressions (string characters)
	 for (unsigned int i=0; i<dcdt.size(); i++) // i is line index, i.e dc_i/dt function
	 {
	 	// loop over each entity
		for (unsigned int j=0; j<dcdt.size(); j++) // j is column index, i.e entities as variables
		{
			string var = "c" + to_string(j);
			string partial = PartialDerivate(dcdt[i], var);
			strJacobiMatrix.getReference(i).getReference(j) = partial;
			//cout << "\t("<<i<<j<<") " + var + "  " + partial << "\t\t" << strJacobiMatrix[i][j] << endl;

		}
	}


	// // sanity check
	// for (auto& cp : dcdt) cout << cp << endl;
	// cout << endl;
	// for (auto& line : strJacobiMatrix)
	// {
	// 	for (auto& el : line) cout << el << ";;\t";
	// 	cout << endl;
	// }

	// test evaluate jacobi matrix
	Array<float> witness = {1., 2., 3., 4.};
	Array<Array<float>> jacobiMatrix = evaluateJacobiMatrix(witness);


  // sanity check
	for (auto& line : jacobiMatrix)
	{
		for (auto& el : line) cout << el << "\t";
		cout << endl;
	}
	

} // end computeJacobiMatrix





// Function to check if a character is an operator
bool isOperator(char c) {
    return (c == '+' || c == '-' || c == '*' || c == '/');
}

// Fonction pour effectuer une opération entre deux opérandes
float applyOperation(float a, float b, char op) {
    switch (op) {
        case '+':
            return (a + b);
        case '-':
            return (a - b);
        case '*':
            return (a * b);
        case '/':
            if (b != 0)
                return (a / b);
            else
                throw  juce::OSCFormatError("Division par zéro !");
        default:
            throw juce::OSCFormatError("Opérateur invalide !");
    }
}



// Fonction pour évaluer une expression formelle
float evaluateExpression(const string& expr)
{
	// case where string to evaluate starts with '+' or '-' will be pathological
	// --> add operand '0.' at the beginning of the string
	string expression = expr;
  if (expression[0] == '-' || expression[0] == '+') expression = "0." + expression;

  stack<float> operandStack;
  stack<char> operatorStack;

  for (size_t i = 0; i < expression.length(); ++i)
	{
    if (expression[i] == ' ') continue; // Ignore spaces

    if (isdigit(expression[i])) // first case : character is a digit
		{
      // Extract operand of expression
      string operandStr;
      while (i < expression.length() && (isdigit(expression[i]) || expression[i]=='.' )) 
			{
       	operandStr += expression[i];
        i++;
      }
      i--;

			// convert current chain into a float and put it in the operand stack
      operandStack.push(stof(operandStr));
			//cout << "\tadded operand " << operandStr << " converted to " << stof(operandStr) << endl;
    } 

		else if (expression[i] == '(') // 2nd case : open bracket --> put it in the operator stack
		{
      operatorStack.push(expression[i]);
    } 

		else if (expression[i] == ')')  // 3rd case : closing bracket
		{
			// when encountering a closing brancket, perform operations downward until open bracket is reached
      while (!operatorStack.empty() && operatorStack.top() != '(')
			{
        char op = operatorStack.top(); // get most upstream operator
        operatorStack.pop(); // remove it from the stack

				// get two most upstream operands
        float operand2 = operandStack.top(); 
        operandStack.pop();
        float operand1 = operandStack.top();
        operandStack.pop();

				// perform operation, then stack it
        operandStack.push(applyOperation(operand1, operand2, op));
      }

      // Pop opening bracket
      if (!operatorStack.empty()) operatorStack.pop();
      else // pathological case
			{
				LOG("Warning : found non paired bracket in formal expression --> return 0. Jacobi Matrix is suspect");
				return 0.;
			}
    } // end closing bracket case


		// 4th case : when encountering an operator, perform calculation respecting priority rules
		else if (isOperator(expression[i])) 
		{
      while (!operatorStack.empty() && 
             isOperator(operatorStack.top()) && 
             ((expression[i] != '*' && expression[i] != '/') || 
             (operatorStack.top() == '*' || operatorStack.top() == '/'))) 
			{
       	char op = operatorStack.top();
       	operatorStack.pop();

       	float operand2 = operandStack.top();
       	operandStack.pop();

       	float operand1 = operandStack.top();
       	operandStack.pop();

       	operandStack.push(applyOperation(operand1, operand2, op));

				//cout << "op --> " << operand1 << " " << op << " " << operand2 << " = " << applyOperation(operand1, operand2, op) << endl;

    	}

      // Mettre l'opérateur dans la pile des opérateurs
      operatorStack.push(expression[i]);
    } 
		
		else 
		{
			string bad = {expression[i]};
      LOG("Warning : non-valid caracter in expression, return 0. ! Bad wharacter is : '" + bad + "'");
			return 0.;
    }

  } // end for loop over characters of string expression

    // Perform remaining operations
    while (!operatorStack.empty()) 
		{
      char op = operatorStack.top();
      operatorStack.pop();

      float operand2 = operandStack.top();
      operandStack.pop();

      float operand1 = operandStack.top();
      operandStack.pop();

      operandStack.push(applyOperation(operand1, operand2, op));

			//cout << "op --> " << operand1 << " " << op << " " << operand2 << " = " << applyOperation(operand1, operand2, op) << endl;
    }

    // operand stack eventually contains result of operations
		///cout << expression << " = " << operandStack.top() << endl;
    if (!operandStack.empty()) return operandStack.top();
    else 
		{
			LOG("Warning : Problem when evaluating string expression");
			return 0.;
		}
} // end func






Array<Array<float>> SteadyStateslist::evaluateJacobiMatrix(Array<float> witness)
{		
	Array<Array<float>> nullJacobiMatrix;
	Array<Array<float>> jacobiMatrix;
	// init jacobi matrix as null matrix
	for (unsigned int i=0; i<strJacobiMatrix.size(); i++)
	{
		Array<float> line;
		for (unsigned int j=0; j<strJacobiMatrix.size(); j++) line.add(0.);
		nullJacobiMatrix.add(line);
	}
	jacobiMatrix = nullJacobiMatrix;


	for (unsigned int i=0; i<strJacobiMatrix.size(); i++)
	{
		for (unsigned int j=0; j<strJacobiMatrix.getReference(i).size(); j++) // a bit overkilled, Jacobi Matrix should be square and its size correct
		{
			string expression = strJacobiMatrix.getReference(i).getReference(j);

			//cout << "will evaluate string '" << expression << "'" << endl;
 
			// replace variables c_i by their numerical values contained in witness
			for (int k=0; k<strJacobiMatrix.size(); k++)
			{
				string var = "c" + to_string(k);
				while (expression.find(var.c_str()) != expression.npos)
				{
					expression.replace(expression.find(var.c_str()), var.size(), to_string(witness[k]));
				}
			}

			float eval = evaluateExpression(expression);
			jacobiMatrix.getReference(i).getReference(j) = eval;
		} // end loop over Jacobi matrix columns
	} // end loop over Jacobi matrix lines

  return jacobiMatrix;

} // end func




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
