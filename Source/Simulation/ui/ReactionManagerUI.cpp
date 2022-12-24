

#include "ReactionManagerUI.h"

ReactionManagerUI::ReactionManagerUI() :
	BaseManagerShapeShifterUI(ReactionManager::getInstance()->niceName, ReactionManager::getInstance())
{
	addExistingItems();
}

ReactionManagerUI::~ReactionManagerUI()
{
}
