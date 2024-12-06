#include "Settings.h"
#include "Entity.h"
#include "Simulation.h"

Entity::Entity(var params) :
	BaseItem(getTypeString() + " 1")
{
	primary = addBoolParameter("Primary", "Is the entity primary ?", true);
	creationRate = addFloatParameter("Creation rate", "Creation rate of the entity", .1f, .0f, 100.f);          // absolute
	destructionRate = addFloatParameter("Destruction rate", "Destruction rate of the entity", .1f, .0f, 100.f); // proportional to concentration
	startConcent = addFloatParameter("Start Concent.", "Start Concentration of the entity", .5f, .0f, 100.f);
	concent = addFloatParameter("Concentration", "Concentration of the entity", .5f, .0f);
	freeEnergy = addFloatParameter("Free energy", "Free energy of the entity", 0.f, -20.f, 20.f);
	draw = addBoolParameter("Draw", "Draw the entity", true);
	setHasCustomColor(true);
}

Entity::Entity(SimEntity* e) :
	Entity(var())
{
	setNiceName(e->name);
	primary->setValue(e->primary);
	creationRate->setValue(e->creationRate);
	destructionRate->setValue(e->destructionRate);
	startConcent->setValue(e->startConcent);
	concent->setValue(e->concent);
	freeEnergy->setValue(e->freeEnergy);
	itemColor->setColor(e->color);
	colorIsSet = true;
	e->entity = this;
	level = e->level;
	id = e->id;
	draw->setValue(e->draw);
}


Entity::~Entity()
{
	composition.clear();
}
