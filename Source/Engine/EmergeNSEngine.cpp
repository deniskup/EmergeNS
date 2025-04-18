

#include "EmergeNSEngine.h"
#include "Simulation/EntityManager.h"
#include "Simulation/ReactionManager.h"
#include "Simulation/Simulation.h"
#include "Simulation/Generation.h"
#include "Simulation/Settings.h"
#include "Simulation/Statistics.h"
#include "Simulation/Space.h"

EmergeNSEngine::EmergeNSEngine() : Engine(ProjectInfo::projectName, ".ens")

{

	Engine::mainEngine = this;
	addChildControllableContainer(Simulation::getInstance());
	addChildControllableContainer(EntityManager::getInstance());
	addChildControllableContainer(ReactionManager::getInstance());
	addChildControllableContainer(Generation::getInstance());
  addChildControllableContainer(Settings::getInstance());
	addChildControllableContainer(PhasePlane::getInstance());
	addChildControllableContainer(Space::getInstance());
}

EmergeNSEngine::~EmergeNSEngine()
{
	isClearing = true;
	Statistics::deleteInstance();
	Simulation::deleteInstance();
	EntityManager::deleteInstance();
	ReactionManager::deleteInstance();
	Generation::deleteInstance();
  Settings::deleteInstance();
	PhasePlane::deleteInstance();
	Space::deleteInstance();

}

void EmergeNSEngine::clearInternal()
{
	Simulation::getInstance()->clearParams();
	EntityManager::getInstance()->clear();
	ReactionManager::getInstance()->clear();
	// Generation::getInstance()->clear();
}


//the bool returned says whether a file has been loaded
bool EmergeNSEngine::parseCommandline(const String& commandLine)
{
	// Call parent function
	bool parentCall = Engine::parseCommandline(commandLine);
	//this contains already several command option like
	// -headless : run the engine without GUI
	// -f "path/to/file.ens": load the file with absolute path

	//Compile with task MakeRelease for better performance

	bool fileLoaded = false;

	// Check if the argument is "config"
	if (commandLine.contains("config"))
	{
		// parameters to give the model
		string z3path = "";
		//int maxlevel;
		//float connection;

		// map of config parameters and their values
		map<string, string> configs;


		// loop over command lines but retrieve only config command
		for (auto& c : StringUtil::parseCommandLine(commandLine))
		{
			if (c.command == "config")
			{
				String fileArg = c.args[0];
				cout << "will open file : " << fileArg << endl;


				// open the config file
				ifstream file;
				file.open(fileArg.toUTF8(), ios::in);
				//file.open(filename.c_str(), ios::in);
				if (!file.is_open())
				{
					LOGERROR("can't open config file : " << fileArg);
					JUCEApplication::getInstance()->systemRequestedQuit();
				}
				fileLoaded = true;
				// store content of config file
				//vector<vector<string>> configs; // config file content stored here
				vector<string> row;
				string line, element;

				// start parsing the config file
				while (getline(file, line))
				{
					row.clear();
					stringstream str(line);
					while (getline(str, element, ':'))
					{
						while (element.find_first_of(' ') != element.npos) element.erase(element.find_first_of(' '), 1); // ignore spaces
						row.push_back(element);
					}

					if (row.size() != 2)
					{
						LOGERROR("config file format issue");
						jassertfalse;
					}
					configs[row[0]] = row[1];
				}
			} //end if is config command line
		} // end command loop

		string model2file = "model.txt";

		// Set model parameters according to config values
		for (auto& [key, val] : configs)
		{
			juce::var myvar(val);
			if (key == "z3path")	Settings::getInstance()->pathToz3->setValueInternal(myvar);
			else if (key == "z3timeout")	Settings::getInstance()->z3timeout->setValueInternal(myvar);
			else if (key == "maxlevel") Generation::getInstance()->numLevels->setValueInternal(myvar);
			else if (key == "connectedness") Generation::getInstance()->propReactions->setValueInternal(myvar);
			else if (key == "Nprimaries") Generation::getInstance()->primEntities->setValueInternal(myvar);
			else if (key == "model2file") model2file = val;
			else if (key == "printPACsToFile")Settings::getInstance()->printPACsToFile->setValueInternal(myvar);
			//else if (key=="connectedness")
		}

		// Generate a reaction network
		//Simulation::Simulation * simu = new Simulation::Simulation();
		Simulation::getInstance()->fetchGenerate();

		DBG("num per level : " + Generation::getInstance()->entPerLevNum->stringValue());

		// write model to txt file
		//Simulation::getInstance()->PrintSimuToFile(model2file.c_str());

		// Compute the PACs with z3
		// doesn't work for the moment
		Simulation::getInstance()->pacList->compute(2);

		// Run the simulation
		//Simulation::getInstance()->run();

		// Output the results in a file
		//String outputFilePath = "simulation_results.txt";
		//Simulation::getInstance()->outputResults(outputFilePath);

		// Print a message when finished
		//cout << "Simulation completed. Results saved in " << outputFilePath << std::endl;
		//quit application



		JUCEApplication::getInstance()->systemRequestedQuit();


	}


	return (fileLoaded || parentCall);

}


var EmergeNSEngine::getJSONData(bool includeNonOverriden)
{
	var data = Engine::getJSONData();
	data.getDynamicObject()->setProperty(Simulation::getInstance()->shortName, Simulation::getInstance()->getJSONData());
	data.getDynamicObject()->setProperty(EntityManager::getInstance()->shortName, EntityManager::getInstance()->getJSONData());
	data.getDynamicObject()->setProperty(ReactionManager::getInstance()->shortName, ReactionManager::getInstance()->getJSONData());
	data.getDynamicObject()->setProperty(Generation::getInstance()->shortName, Generation::getInstance()->getJSONData());
	data.getDynamicObject()->setProperty(Settings::getInstance()->shortName, Settings::getInstance()->getJSONData());
  data.getDynamicObject()->setProperty(PhasePlane::getInstance()->shortName, PhasePlane::getInstance()->getJSONData());
  data.getDynamicObject()->setProperty(Space::getInstance()->shortName, Space::getInstance()->getJSONData());
  data.getDynamicObject()->setProperty("currentSimul", Simulation::getInstance()->toJSONData());

	return data;
}

void EmergeNSEngine::loadJSONDataInternalEngine(var data, ProgressTask* loadingTask)
{
	Simulation::getInstance()->loadJSONData(data.getProperty(Simulation::getInstance()->shortName, var()));
	EntityManager::getInstance()->loadJSONData(data.getProperty(EntityManager::getInstance()->shortName, var()));
	ReactionManager::getInstance()->loadJSONData(data.getProperty(ReactionManager::getInstance()->shortName, var()));
	Generation::getInstance()->loadJSONData(data.getProperty(Generation::getInstance()->shortName, var()));
  Settings::getInstance()->loadJSONData(data.getProperty(Settings::getInstance()->shortName, var()));
  PhasePlane::getInstance()->loadJSONData(data.getProperty(PhasePlane::getInstance()->shortName, var()));
  Space::getInstance()->loadJSONData(data.getProperty(Space::getInstance()->shortName, var()));
	Simulation::getInstance()->importJSONData(data.getProperty("currentSimul", var()));

	//Simulation::getInstance()->establishLinks();

}

String EmergeNSEngine::getMinimumRequiredFileVersion()
{
	return "1.0.0";
}
