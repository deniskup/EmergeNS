/*
  ==============================================================================

	EmergenceNSEngine.cpp
	Created: 5 Apr 2022 10:35:04am
	Author:  bkupe

  ==============================================================================
*/

#include "EmergenceNSEngine.h"
#include "Simulation/EntityManager.h"
#include "Simulation/Simulation.h"

EmergenceNSEngine::EmergenceNSEngine() :
	Engine(ProjectInfo::projectName, ".ens")

{

	
	Engine::mainEngine = this;
	addChildControllableContainer(Simulation::getInstance());
	addChildControllableContainer(EntityManager::getInstance());
	
}

EmergenceNSEngine::~EmergenceNSEngine()
{
	isClearing = true;

	
	Simulation::deleteInstance();
	EntityManager::deleteInstance();
}

void EmergenceNSEngine::clearInternal()
{
	//Simulation::getInstance()->cancel();
	EntityManager::getInstance()->clear();
}



var EmergenceNSEngine::getJSONData()
{
	var data = Engine::getJSONData();
	data.getDynamicObject()->setProperty(Simulation::getInstance()->shortName, Simulation::getInstance()->getJSONData());
	data.getDynamicObject()->setProperty(EntityManager::getInstance()->shortName, EntityManager::getInstance()->getJSONData());
	return data;
}

void EmergenceNSEngine::loadJSONDataInternalEngine(var data, ProgressTask* loadingTask)
{
	Simulation::getInstance()->loadJSONData(data.getProperty(Simulation::getInstance()->shortName, var()));
	EntityManager::getInstance()->loadJSONData(data.getProperty(EntityManager::getInstance()->shortName, var()));
}

String EmergenceNSEngine::getMinimumRequiredFileVersion()
{
	return "1.0.0";
}

