

#include "EntityManagerUI.h"

EntityManagerUI::EntityManagerUI() :
	BaseManagerShapeShifterUI(EntityManager::getInstance()->niceName, EntityManager::getInstance())
{
	addExistingItems();
	//todo: if not primary, remove creation rate.

}

EntityManagerUI::~EntityManagerUI()
{
}
