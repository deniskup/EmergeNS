

#include "EmergeNSEngine.h"
//#include "Simulation/EntityManager.h"
//#include "Simulation/ReactionManager.h"
//#include "Simulation/Simulation.h"
//#include "Simulation/Generation.h"
//#include "Simulation/Settings.h"
//#include "Simulation/Statistics.h"

bool to_bool(std::string& x) {
  // removed space from x
  while (x.find(" ") != x.npos)
    x.erase(x.find(" "), 1);
  //cout << "x = " << x << endl;
  assert(x == "0" || x == "1");
  return x == "1";
}

EmergeNSEngine::EmergeNSEngine() : Engine(ProjectInfo::projectName, ".ens")

{

	Engine::mainEngine = this;
	addChildControllableContainer(Simulation::getInstance());
	addChildControllableContainer(EntityManager::getInstance());
	addChildControllableContainer(ReactionManager::getInstance());
	addChildControllableContainer(Generation::getInstance());
  addChildControllableContainer(Settings::getInstance());
	addChildControllableContainer(PhasePlane::getInstance());
  //Simulation::getInstance()->setListener(this);
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

      else if (c.command == "srun")
      {
        String str = c.args[0];
        superRun = atoi(str.toUTF8());
      }
		} // end command loop

		string model2file = "model.txt";

		// Set model parameters according to config values
		for (auto& [key, val] : configs)
		{
      //cout << "key, val : " << key << " " << val << endl;
			juce::var myvar(val);
			if (key == "z3path")	Settings::getInstance()->pathToz3->setValueInternal(myvar);
			else if (key == "z3timeout")	Settings::getInstance()->z3timeout->setValueInternal(myvar);
			else if (key == "maxlevel") Generation::getInstance()->numLevels->setValueInternal(myvar);
			else if (key == "connectedness") Generation::getInstance()->propReactions->setValueInternal(myvar);
			else if (key == "Nprimaries") Generation::getInstance()->primEntities->setValueInternal(myvar);
			else if (key == "model2file") model2file = val;
      else if (key == "printPACsToFile")Settings::getInstance()->printPACsToFile->setValueInternal(myvar);
      else if (key == "study") study = String(val);
      else if (key == "totalTime") totalTime = atof(val.c_str());
      else if (key == "dt") dt = atof(val.c_str());
      else if (key == "epsilonNoise") epsilonNoise = atof(val.c_str());
      else if (key == "nRuns") nRuns = atoi(val.c_str());
      else if (key == "network") filename = String(val);
      else if (key == "fixedSeed") fixedSeed = to_bool(val);
      else if (key == "seed") seed = atoi(val.c_str());
      else if (key == "dtbis") dtbis = atof(val.c_str());
      else if (key == "nstepbis") nstepbis = atoi(val.c_str());
      else if (key == "exitTimePrecision") exitTimePrecision = atof(val.c_str());
      else if (key == "epsilon") epsilon = atof(val.c_str());
      else if (key == "maxsteps_study") maxsteps_study = atoi(val.c_str());
      else if (key == "outputfilename") outputfilename = val.c_str();
      else if (key == "dtsave") dtsave = atof(val.c_str());
      else if (key == "startSteadyState") startSteadyState = String(val);
      //else if (key == "superRun") superRun = atoi(val.c_str());
		}
    
    
    if (study == "firstExit")
    {
      juce::File file(filename);
      GlobalSettings::getInstance()->logAutosave->setValue(false);
      loadDocumentNoCheck(file);
      
      // desactivate autosave
      GlobalSettings::getInstance()->enableAutoSave->setValue(false);
      //GlobalSettings::getInstance()->logAutosave->setValue(false);
      
      // tp print history to file
      Settings::getInstance()->printHistoryToFile->setValue(true);
      
      // set simulation instance parameters according to those of
      Simulation::getInstance()->exitTimeStudy = true;
      Simulation::getInstance()->transitStudy = false;
      Simulation::getInstance()->totalTime->setValue(totalTime);
      Simulation::getInstance()->dt->setValue(dt);
      Settings::getInstance()->volume->setValue(-2.*log10(epsilonNoise));
      Settings::getInstance()->fixedSeed->setValue(fixedSeed);
      Settings::getInstance()->randomSeed->setValue(seed);
      Simulation::getInstance()->dtbis = dtbis;
      Simulation::getInstance()->maxsteps_study = maxsteps_study;
      Simulation::getInstance()->exitTimePrecision = exitTimePrecision;
      Simulation::getInstance()->epsilon = epsilon;
      Simulation::getInstance()->outputfilename = outputfilename;
      Simulation::getInstance()->superRun = superRun;
      
      // additionnal configurations
      Simulation::getInstance()->autoScale->setValue(true);
      Simulation::getInstance()->stochasticity->setValue(true);
      Simulation::getInstance()->noVisu = true;
      
      firstExitTimeStudy();
    }
    else if (study == "transit")
    {
      juce::File file(filename);
      GlobalSettings::getInstance()->logAutosave->setValue(false);
      loadDocumentNoCheck(file);
      
      // desactivate autosave
      GlobalSettings::getInstance()->enableAutoSave->setValue(false);
      //GlobalSettings::getInstance()->logAutosave->setValue(false);
      // tp print history to file
      Settings::getInstance()->printHistoryToFile->setValue(true);
      
      // set simulation instance parameters according to those of
      Simulation::getInstance()->exitTimeStudy = false;
      Simulation::getInstance()->transitStudy = true;
      Simulation::getInstance()->totalTime->setValue(totalTime);
      Simulation::getInstance()->dt->setValue(dt);
      Settings::getInstance()->volume->setValue(-2.*log10(epsilonNoise));
      Settings::getInstance()->fixedSeed->setValue(fixedSeed);
      Settings::getInstance()->randomSeed->setValue(seed);
      Simulation::getInstance()->dtbis = dtbis;
      Simulation::getInstance()->dtsave = dtsave;
      Simulation::getInstance()->maxsteps_study = maxsteps_study;
      Simulation::getInstance()->exitTimePrecision = exitTimePrecision;
      Simulation::getInstance()->epsilon = epsilon;
      Simulation::getInstance()->outputfilename = outputfilename;
      Simulation::getInstance()->superRun = superRun;
      Simulation::getInstance()->startAC = startSteadyState;
      
      // additionnal configurations
      Simulation::getInstance()->stochasticity->setValue(true);
      Simulation::getInstance()->noVisu = true;
      
      transitStudy();
      
    }
    
    
    else if (study == "paccac")
    {
      // Generate a reaction network
      //Simulation::Simulation * simu = new Simulation::Simulation();
      Simulation::getInstance()->fetchGenerate();

      DBG("num per level : " + Generation::getInstance()->entPerLevNum->stringValue());

      // write model to txt file
      //Simulation::getInstance()->PrintSimuToFile(model2file.c_str());

      // Compute the PACs with z3
      // doesn't work for the moment
      Simulation::getInstance()->pacList->compute(2);
    }


    else if (study == "sstCompo")
    {
      steadyStateCompositionStudy();
    }

		

		// Run the simulation
		//Simulation::getInstance()->run();

		// Output the results in a file
		//String outputFilePath = "simulation_results.txt";
		//Simulation::getInstance()->outputResults(outputFilePath);

		// Print a message when finished
		//cout << "Simulation completed. Results saved in " << outputFilePath << std::endl;
		//quit application


/*
    //JUCEApplication::getInstance()->systemRequestedQuit();
    while (Simulation::getInstance()->isThreadRunning())
    {
          //Simulation::getInstance()->signalThreadShouldExit();
      Simulation::getInstance()->waitForThreadToExit(10000); // 10s de patience cosmique
    }
    */

    //cout << "is running ? -> " << Simulation::getInstance()->state << endl;
    //Simulation::getInstance()->~Simulation();
		//JUCEApplication::getInstance()->quit();


	} // end if config


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
	Simulation::getInstance()->importJSONData(data.getProperty("currentSimul", var()));

	//Simulation::getInstance()->establishLinks();

}

String EmergeNSEngine::getMinimumRequiredFileVersion()
{
	return "1.0.0";
}


// FOLLOWING is some code to measure statistically the robustness of a steady state


void EmergeNSEngine::firstExitTimeStudy()
{
  
  if (Simulation::getInstance()->steadyStatesList->arraySteadyStates.size() == 0)
  {
    LOG("should calculate steady states and save the file, for now I just leave the function.");
    return;
  }
  
  // set concentration of entities to the one of steady state
  SteadyState startSST;
  int indexStartSST = -1;
  
  int c=-1;
  for (auto & sst : Simulation::getInstance()->steadyStatesList->arraySteadyStates)
  {
    c++;
    //SteadyStateslist::getInstance()->printOneSteadyState(sst);
    if (sst.isBorder)
      continue;
    
    // choose the steady state A or B dominated
    float totA = 0.;
    for (auto & [ent, c] : sst.state)
    {
      if (c>100)
        break;
      if (ent->name.contains(startSteadyState))
        totA += c;
    }
    //cout << "total A species = " << totA << ". index sst = " << c << endl;
    if (totA > 100) // avoid pathological steady states found
      continue;
    if (totA>0.1)
    {
      startSST = sst;
      indexStartSST = c;
      break;
    }
  }
  
  //cout << "picked sst index " << indexStartSST << endl;
  
  
  // set startConc to this steady state
  if (indexStartSST>=0)
  {
    //SteadyStateslist::getInstance()->printOneSteadyState(startSST);
    Simulation::getInstance()->setConcToSteadyState(indexStartSST+1, true);
    Simulation::getInstance()->startSST = indexStartSST;
    //Simulation::getInstance()->curSST = indexStartSST;
  }
  else
  {
    LOG("Cannot find matching steady state, stop.");
    return;
  }
  // just in case
  Simulation::getInstance()->generateSimFromUserList();
  
  
  
  // init runs
  PhasePlane::getInstance()->clearAllRuns();
  PhasePlane::getInstance()->nRuns->setValue(nRuns);
  PhasePlane::getInstance()->updateEntitiesFromSimu();
  
  // start simulation
  PhasePlane::getInstance()->startRuns();
  
  
  
}





void EmergeNSEngine::transitStudy()
{
  
  if (Simulation::getInstance()->steadyStatesList->arraySteadyStates.size() == 0)
  {
    LOG("should calculate steady states and save the file, for now I just leave the function.");
    return;
  }
  
  // set concentration of entities to the one of steady state
  SteadyState startSST;
  int indexStartSST = -1;
  
  int c=-1;
  for (auto & sst : Simulation::getInstance()->steadyStatesList->arraySteadyStates)
  {
    c++;
    //SteadyStateslist::getInstance()->printOneSteadyState(sst);
    if (sst.isBorder)
      continue;
    
    // choose the steady state A or B dominated
    float totA = 0.;
    for (auto & [ent, c] : sst.state)
    {
      if (c>100)
        break;
      if (ent->name.contains(startSteadyState))
        totA += c;
    }
    //cout << "total A species = " << totA << ". index sst = " << c << endl;
    if (totA > 100) // avoid pathological steady states found
      continue;
    if (totA>0.1)
    {
      startSST = sst;
      indexStartSST = c;
      break;
    }
  }
    
  
  // set startConc to this steady state
  if (indexStartSST>=0)
  {
    //SteadyStateslist::getInstance()->printOneSteadyState(startSST);
    Simulation::getInstance()->setConcToSteadyState(indexStartSST+1, true);
    Simulation::getInstance()->startSST = indexStartSST;
    //Simulation::getInstance()->curSST = indexStartSST;
  }
  else
  {
    LOG("Cannot find matching steady state, stop.");
    return;
  }
  // just in case
  Simulation::getInstance()->generateSimFromUserList();
  
  
  
  // init runs
  PhasePlane::getInstance()->clearAllRuns();
  PhasePlane::getInstance()->nRuns->setValue(nRuns);
  PhasePlane::getInstance()->updateEntitiesFromSimu();
  
  // start simulation
  PhasePlane::getInstance()->startRuns();
  
  
  
}




void EmergeNSEngine::steadyStateCompositionStudy()
{
  vector<float> barrB = {1., 1.05, 1.1, 1.15, 1.2};
  vector<float> feB = {0., 0.05, 0.1, 0.15, 0.2};

  string out = "B barrier,B free energy,sstType,massA,massB\n";

  for (float & b : barrB)
  {
    // set barriers of reactions of cycle B
    for (auto & r : Simulation::getInstance()->reactions)
    {
      if (r->name.contains("Fb"))
        r->energy = b;
    }
    for (float & fe : feB)
    {
      for (auto & e : Simulation::getInstance()->entities)
      {
        if (e->name == "Fb")
          e->freeEnergy = fe;
      }
    }

    // calculate steady state compo with msolve
    Simulation::getInstance()->steadyStatesList->computeSteadyStates();

    for (auto & sst : Simulation::getInstance()->steadyStatesList->arraySteadyStates)
    {
      if (sst.isBorder) // remove border steady states
        continue;

      float masstot = 0.;
      float massA = 0.;
      float massB = 0.;
      for (auto & p : sst.state)
      {
        masstot += p.second;
        if (p.first->name == "A1" || p.first->name == "A2" || p.first->name == "Wa")
          massA += p.second;
        if (p.first->name == "=B1" || p.first->name == "B2" || p.first->name == "Wb")
          massB += p.second;
      }
      if (masstot>100.) // remove steady states which are too high, happens sometimes
        continue;

      // "B barrier,B free energy,sstType,massA,massB\n";
      out += to_string(b) + "," + to_string(fe) + ",";
      if (massA > massB)
        out += "A," + to_string(massA) + to_string(massB);
      else
        out += "B," + to_string(massA) + to_string(massB);
      out += "\n";
    }
  }
}

