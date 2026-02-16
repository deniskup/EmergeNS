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
  
  startConcent->isSavable = false;
  concent->isSavable = false;
}

void Entity::updateInterface()
{
	creationRate->setControllableFeedbackOnly(chemostat->boolValue() || !primary->boolValue());
	creationRate->hideInEditor = chemostat->boolValue() || !primary->boolValue();
	destructionRate->setControllableFeedbackOnly(chemostat->boolValue());
	destructionRate->hideInEditor = chemostat->boolValue();
	concent->setControllableFeedbackOnly(chemostat->boolValue());
	concent->hideInEditor = chemostat->boolValue();
	queuedNotifier.addMessage(new ContainerAsyncEvent(ContainerAsyncEvent::ControllableContainerNeedsRebuild, this));
}

//Entity::Entity(SimEntity *e) : Entity(var())
Entity::Entity(SimEntity *e, int patchid) : Entity(var())
{
	setNiceName(e->name);
	primary->setValue(e->primary);
	creationRate->setValue(e->creationRate);
	destructionRate->setValue(e->destructionRate);
  
	startConcent->setValue(e->startConcent[patchid]);
	concent->setValue(e->concent[patchid]);
  
	freeEnergy->setValue(e->freeEnergy);
	itemColor->setColor(e->color);
	colorIsSet = true;
	e->entity = this;
	level = e->level;
	id = e->id;
	simEnt = e;
	draw->setValue(e->draw);
}

void Entity::onContainerParameterChanged(Parameter *p)
{
  //cout << "Listener being called !" << endl;
	if (p == chemostat)
	{
		updateInterface();
	}
  else if (p == concent || p == startConcent) 
  {
    if (p==concent)
      cout << "Changed concentration. Val = " << concent->floatValue() << endl;
    if (!Engine::mainEngine->isLoadingFile && updateSimEntityOnValueChanged)
    {
      //simEnt = Simulation::getInstance()->getSimEntityForName(niceName);
      if (simEnt)
        simEnt->updateFromEntity(this);
    }
  }
  else
  {
    if(simEnt)
    {
      simEnt->updateFromEntity(this);
    }
  }
}

Entity::~Entity()
{
	composition.clear();
}
