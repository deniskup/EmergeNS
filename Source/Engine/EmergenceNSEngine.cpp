

#include "EmergenceNSEngine.h"
#include "Simulation/EntityManager.h"
#include "Simulation/ReactionManager.h"
#include "Simulation/Simulation.h"
#include "Simulation/Generation.h"
#include "Simulation/Settings.h"
#include "Simulation/Statistics.h"

EmergenceNSEngine::EmergenceNSEngine() : Engine(ProjectInfo::projectName, ".ens")

{

	Engine::mainEngine = this;
	addChildControllableContainer(Simulation::getInstance());
	addChildControllableContainer(EntityManager::getInstance());
	addChildControllableContainer(ReactionManager::getInstance());
	addChildControllableContainer(Generation::getInstance());
	addChildControllableContainer(Settings::getInstance());
}

EmergenceNSEngine::~EmergenceNSEngine()
{
	isClearing = true;

	Simulation::deleteInstance();
	EntityManager::deleteInstance();
	ReactionManager::deleteInstance();
	Generation::deleteInstance();
	Settings::deleteInstance();
	Statistics::deleteInstance();
}

void EmergenceNSEngine::clearInternal()
{
	// Simulation::getInstance()->cancel();
	EntityManager::getInstance()->clear();
	ReactionManager::getInstance()->clear();
	// Generation::getInstance()->clear();
}

var EmergenceNSEngine::getJSONData()
{
	var data = Engine::getJSONData();
	data.getDynamicObject()->setProperty(Simulation::getInstance()->shortName, Simulation::getInstance()->getJSONData());
	data.getDynamicObject()->setProperty(EntityManager::getInstance()->shortName, EntityManager::getInstance()->getJSONData());
	data.getDynamicObject()->setProperty(ReactionManager::getInstance()->shortName, ReactionManager::getInstance()->getJSONData());
	data.getDynamicObject()->setProperty(Generation::getInstance()->shortName, Generation::getInstance()->getJSONData());
	data.getDynamicObject()->setProperty(Settings::getInstance()->shortName, Settings::getInstance()->getJSONData());
	data.getDynamicObject()->setProperty("currentSimul", Simulation::getInstance()->toJSONData());

	return data;
}

void EmergenceNSEngine::loadJSONDataInternalEngine(var data, ProgressTask *loadingTask)
{
	Simulation::getInstance()->loadJSONData(data.getProperty(Simulation::getInstance()->shortName, var()));
	EntityManager::getInstance()->loadJSONData(data.getProperty(EntityManager::getInstance()->shortName, var()));
	ReactionManager::getInstance()->loadJSONData(data.getProperty(ReactionManager::getInstance()->shortName, var()));
	Generation::getInstance()->loadJSONData(data.getProperty(Generation::getInstance()->shortName, var()));
	Settings::getInstance()->loadJSONData(data.getProperty(Settings::getInstance()->shortName, var()));
	Simulation::getInstance()->importJSONData(data.getProperty("currentSimul", var()));
}

String EmergenceNSEngine::getMinimumRequiredFileVersion()
{
	return "1.0.0";
}
