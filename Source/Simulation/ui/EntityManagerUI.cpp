

#include "EntityManagerUI.h"

EntityManagerUI::EntityManagerUI() :
	BaseManagerShapeShifterUI(EntityManager::getInstance()->niceName, EntityManager::getInstance())
{
	addExistingItems();
}

EntityManagerUI::~EntityManagerUI()
{
}
