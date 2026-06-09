

#include "EmergeNSEngine.h"
#include "Simulation/EntityManager.h"
#include "Simulation/ReactionManager.h"
#include "Simulation/Simulation.h"
#include "Simulation/Generation.h"
#include "Simulation/Settings.h"
#include "Simulation/Statistics.h"
#include "Simulation/Space.h"
#include "Simulation/NEP.h"
using namespace juce;

std::vector<float> lineSpace(float inf, float sup, float step){
    std::vector<float> vec;
    if (step <= 0) { vec.push_back(inf); return vec; }
    for(float val = inf; val <= sup; val += step){
        vec.push_back(val);
    }
    return vec;
}

std::string floatToFolderName(float f) {
    float rounded = std::round(f * 100000.f) / 100000.f;
    std::ostringstream oss;
    oss << std::fixed << std::setprecision(5) << std::abs(rounded);
    std::string s = oss.str();
    std::replace(s.begin(), s.end(), '.', 'p');
    if (rounded < 0.f) s = "m" + s;
    return s;
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
  addChildControllableContainer(Space::getInstance());
	addChildControllableContainer(NEP::getInstance());
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
	NEP::deleteInstance();
}

void EmergeNSEngine::clearInternal()
{
  Simulation::getInstance()->clearParams();
  EntityManager::getInstance()->clear();
  ReactionManager::getInstance()->clear();
  // Generation::getInstance()->clear();
}



std::map<String, String> EmergeNSEngine::parseConfigFile(String fileArg)
{
  
  //cout << "will open file : " << fileArg << endl;

  std::map<String, String> configs;

  // open the config file
  ifstream file;
  file.open(fileArg.toUTF8(), ios::in);
  //file.open(filename.c_str(), ios::in);
  if (!file.is_open())
  {
    LOGERROR("can't open config file : " << fileArg);
    std::cerr << "errno = " << errno << std::endl;
    std::cerr << strerror(errno) << std::endl;
    JUCEApplication::getInstance()->systemRequestedQuit();
  }
  //fileLoaded = true;
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

//cout << "end config file reading" << endl;

return configs;
  
}


//the bool returned says whether a file has been loaded
bool EmergeNSEngine::parseCommandline(const String& commandLine)
{
  // Call parent function
  bool parentCall = Engine::parseCommandline(commandLine);
  //this contains already several command option like
  // -headless : run the engine without GUI
  // -f "path/to/file.ens": load the file with absolute path
  
  cout << "parsing command line" << endl;

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
    map<String, String> configs;


    // loop over command lines but retrieve only config command
    for (auto& c : StringUtil::parseCommandLine(commandLine))
    {
      if (c.command == "config")
      {
        configs = parseConfigFile(c.args[0]);
        fileLoaded = true; // #todo change value by properly handling an exception in parseConfigFile
      }
      else if (c.command == "superRun")
      {
        String command = String(c.command);
        String strval = c.args[0];
        configs[command] = strval;
        //cout << "setting super run to " << strval << endl;
      }
      
    } // end command loop

    String model2file = "model.txt";
    String network = "";

    // Set model parameters according to config values
    for (auto& [key, val] : configs)
    {
      juce::var myvar(val);
      if (key == "z3path")  Settings::getInstance()->pathToz3->setValueInternal(myvar);
      else if (key == "z3timeout")  Settings::getInstance()->z3timeout->setValueInternal(myvar);
      else if (key == "maxlevel") Generation::getInstance()->numLevels->setValueInternal(myvar);
      else if (key == "connectedness") Generation::getInstance()->propReactions->setValueInternal(myvar);
      else if (key == "Nprimaries") Generation::getInstance()->primEntities->setValueInternal(myvar);
      else if (key == "model2file") model2file = val;
      else if (key == "printPACsToFile")Settings::getInstance()->printPACsToFile->setValueInternal(myvar);
      else if (key == "study") study = String(val);
      else if (key == "network") network = val;
      //else if (key=="connectedness")
    }
    
    // open the .ens file
    juce::File file(network);
    loadDocumentNoCheck(file);
    
    
    if (study == "firstEscape")
    {
      firstEscapeTimeStudy(configs);
    }
    else if (study == "steadystates")
    {
        std::vector<float> EB1_vals, EB2_vals, FE1_vals, FE2_vals, FEFa_vals, FEWa_vals;

        float default_EB1 = -1, default_EB2 = -1, default_FE1 = -1, default_FE2 = -1;
        float default_FEFa = 0.f, default_FEWa = 0.f;
        for (auto* sr : Simulation::getInstance()->reactions) {
            if (sr->name == "A1+Fa=A2+Wa")      default_EB1 = sr->energy;
            else if (sr->name == "A2+Fa=A1+A1") default_EB2 = sr->energy;
        }
        for (auto* se : Simulation::getInstance()->entities) {
            if (se->name == "A1")      default_FE1  = se->freeEnergy;
            else if (se->name == "A2") default_FE2  = se->freeEnergy;
            else if (se->name == "Fa") default_FEFa = se->freeEnergy;
            else if (se->name == "Wa") default_FEWa = se->freeEnergy;
        }

        for (auto& [key, val] : configs)
        {
            if (key != "EB1" && key != "EB2" && key != "FE1" && key != "FE2"
                && key != "FEFa" && key != "FEWa") continue;

            std::string inf, sup, nb;
            std::stringstream ss(val.toStdString());
            getline(ss, inf, ';');
            getline(ss, sup, ';');
            getline(ss, nb, ';');
            float v_min = std::stof(inf);
            float v_max = std::stof(sup);
            int   v_nb  = std::stoi(nb);
            std::vector<float> vals = lineSpace(v_min, v_max, (v_max - v_min) / v_nb);

            std::cout << "  -> Parsed " << key << ": min=" << v_min << " max=" << v_max << " nb=" << v_nb
                      << " (" << vals.size() << " valeurs)" << std::endl;

            if      (key == "EB1")  EB1_vals  = vals;
            else if (key == "EB2")  EB2_vals  = vals;
            else if (key == "FE1")  FE1_vals  = vals;
            else if (key == "FE2")  FE2_vals  = vals;
            else if (key == "FEFa") FEFa_vals = vals;
            else if (key == "FEWa") FEWa_vals = vals;
        }

        if (EB1_vals.empty())  EB1_vals  = {default_EB1};
        if (EB2_vals.empty())  EB2_vals  = {default_EB2};
        if (FE1_vals.empty())  FE1_vals  = {default_FE1};
        if (FE2_vals.empty())  FE2_vals  = {default_FE2};
        if (FEFa_vals.empty()) FEFa_vals = {default_FEFa};
        if (FEWa_vals.empty()) FEWa_vals = {default_FEWa};

        std::cout << "EB1_vals  (" << EB1_vals.size()  << "): "; for (float v : EB1_vals)  std::cout << v << " "; std::cout << std::endl;
        std::cout << "EB2_vals  (" << EB2_vals.size()  << "): "; for (float v : EB2_vals)  std::cout << v << " "; std::cout << std::endl;
        std::cout << "FE1_vals  (" << FE1_vals.size()  << "): "; for (float v : FE1_vals)  std::cout << v << " "; std::cout << std::endl;
        std::cout << "FE2_vals  (" << FE2_vals.size()  << "): "; for (float v : FE2_vals)  std::cout << v << " "; std::cout << std::endl;
        std::cout << "FEFa_vals (" << FEFa_vals.size() << "): "; for (float v : FEFa_vals) std::cout << v << " "; std::cout << std::endl;
        std::cout << "FEWa_vals (" << FEWa_vals.size() << "): "; for (float v : FEWa_vals) std::cout << v << " "; std::cout << std::endl;

        std::string networkStr = network.toStdString();
        std::string networkDir = networkStr.substr(0, networkStr.find_last_of("/"));
        std::string resultsDir = networkDir + "/results";
        system(("mkdir -p " + resultsDir).c_str());

        for (float EB1 : EB1_vals){
            for (float EB2 : EB2_vals){
                for (float FE1 : FE1_vals){
                    for (float FE2 : FE2_vals){
                        for (float FEFa : FEFa_vals){
                            for (float FEWa : FEWa_vals){

                                for (auto* se : Simulation::getInstance()->entities){
                                    if (se->name == "A1")      se->freeEnergy = FE1;
                                    else if (se->name == "A2") se->freeEnergy = FE2;
                                    else if (se->name == "Fa") se->freeEnergy = FEFa;
                                    else if (se->name == "Wa") se->freeEnergy = FEWa;
                                }
                                for (auto* sr : Simulation::getInstance()->reactions){
                                    if (sr->name == "A1+Fa=A2+Wa") sr->energy = EB1;
                                    else if (sr->name == "A2+Fa=A1+A1") sr->energy = EB2;
                                    sr->computeRate(false, false);
                                }

                                juce::String outputfile = juce::String(resultsDir)
                                    + "/EB1_"  + floatToFolderName(EB1)
                                    + "_EB2_"  + floatToFolderName(EB2)
                                    + "_FE1_"  + floatToFolderName(FE1)
                                    + "_FE2_"  + floatToFolderName(FE2)
                                    + "_FEFa_" + floatToFolderName(FEFa)
                                    + "_FEWa_" + floatToFolderName(FEWa)
                                    + ".txt";
                                Simulation::getInstance()->steadyStatesList->outputfile = outputfile;

                                Simulation::getInstance()->steadyStatesList->computeSteadyStates();
                                Simulation::getInstance()->steadyStatesList->waitForThreadToExit(-1);

                                juce::File networkFile(network);
                                saveDocument(networkFile);
                            }
                        }
                    }
                }
            }
        }
        JUCEApplication::getInstance()->systemRequestedQuit();
    }
/*
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
    
    */
    //quit application
    



    //JUCEApplication::getInstance()->systemRequestedQuit();


  }


  return (fileLoaded || parentCall);

}


void EmergeNSEngine::firstEscapeTimeStudy(map<String, String> configs)
{
  FirstEscapeTime * fet = new FirstEscapeTime();
  fet->setSimulationConfig(configs);
  fet->startStudy();
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
  data.getDynamicObject()->setProperty(NEP::getInstance()->shortName, NEP::getInstance()->getJSONData());
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
  NEP::getInstance()->loadJSONData(data.getProperty(NEP::getInstance()->shortName, var()));
	Simulation::getInstance()->importJSONData(data.getProperty("currentSimul", var()));

  //Simulation::getInstance()->establishLinks();

}

String EmergeNSEngine::getMinimumRequiredFileVersion()
{
  return "1.0.0";
}
