#include "Settings.h"
#include "Entity.h"
#include "Simulation.h"

Entity::Entity(var params) : BaseItem(getTypeString() + " 1")
{
	primary = addBoolParameter("Primary", "Is the entity primary ?", true);
	chemostat = addBoolParameter("Chemostat", "Is the entity in chemostat ?", false);
	creationRate = addFloatParameter("Creation rate", "Creation rate of the entity", .1f, .0f, 100.f);			// absolute
	destructionRate = addFloatParameter("Destruction rate", "Destruction rate of the entity", .1f, .0f, 100.f); // proportional to concentration
	startConcent = addFloatParameter("Start Concent.", "Start Concentration of the entity", .5f, .0f, 100.f);
	concent = addFloatParameter("Concentration", "Concentration of the entity", .5f, .0f);
	freeEnergy = addFloatParameter("Free energy", "Free energy of the entity", 0.f, -20.f, 20.f);
	draw = addBoolParameter("Draw", "Draw the entity", true);
	setHasCustomColor(true);
	updateInterface();
	primary->hideInEditor = true;
}

void Entity::updateInterface()
{
	creationRate->setControllableFeedbackOnly(chemostat->boolValue());
	creationRate->hideInEditor = chemostat->boolValue();
	destructionRate->setControllableFeedbackOnly(chemostat->boolValue());
	destructionRate->hideInEditor = chemostat->boolValue();
	concent->setControllableFeedbackOnly(chemostat->boolValue());
	concent->hideInEditor = chemostat->boolValue();
	queuedNotifier.addMessage(new ContainerAsyncEvent(ContainerAsyncEvent::ControllableContainerNeedsRebuild, this));
}

Entity::Entity(SimEntity *e) : Entity(var())
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

void Entity::onContainerParameterChanged(Parameter *p)
{
	if (p == chemostat)
	{
		updateInterface();
	}
	if(simEnt)
		simEnt->updateFromEntity(this);
}

Entity::~Entity()
{
	composition.clear();
}
