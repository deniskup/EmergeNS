#include "Settings.h"
#include "Reaction.h"
#include "EntityManager.h"
#include "Simulation.h"

#define CONSTANTS_PRECISION 7

Reaction::Reaction(var params) : BaseItem(getTypeString() + " 1")
{
	addParams();

	// 2->1 by default
	if (!Engine::mainEngine->isLoadingFile)
	{
		addReactant(nullptr);
		addReactant(nullptr);
		addProduct(nullptr);
	}
}


Reaction::Reaction(SimReaction* r) :
	BaseItem(r->name)
{
	addParams();

	for (auto e : r->reactants)
	{
		addReactant(e->entity);
	}

	for (auto e : r->products)
	{
		addProduct(e->entity);
	}

	if (r->energy < -.5f)
		r->computeBarrier();
	energy->setValue(r->energy);
	assocRate->setValue(r->assocRate);
	dissocRate->setValue(r->dissocRate);

	simReac = r;
}


Reaction::~Reaction()
{

}

void Reaction::clearItem()
{
	for (auto& r : getAllReactants())
	{
		if (r == nullptr) continue;
		unregisterLinkedInspectable(r);
		r->enabled->removeParameterListener(this);
		r->freeEnergy->removeParameterListener(this);
	}

	for (auto& p : getAllProducts())
	{
		if (p == nullptr) continue;
		unregisterLinkedInspectable(p);
		p->enabled->removeParameterListener(this);
		p->freeEnergy->removeParameterListener(this);

	}
}

void Reaction::addParams()
{
	saveAndLoadRecursiveData = true;

	reactants.reset(new ControllableContainer("Reactants"));
	reactants->userCanAddControllables = true;
	reactants->userAddControllablesFilters.add(TargetParameter::getTypeStringStatic());
	addChildControllableContainer(reactants.get());

	products.reset(new ControllableContainer("Products"));
	products->userCanAddControllables = true;
	products->userAddControllablesFilters.add(TargetParameter::getTypeStringStatic());
	addChildControllableContainer(products.get());

	energy = addFloatParameter("Energy Barrier", "Additional energy barrier of the reaction", 1.f, 0.f, 100.f);

	assocRate = addFloatParameter("Association rate", "Reaction speed left to right", .5f);
	dissocRate = addFloatParameter("Dissociation rate", "Reaction speed right to left", .5f);
	assocRate->setControllableFeedbackOnly(true);
	dissocRate->setControllableFeedbackOnly(true);
	assocRate->setAttributeInternal("stringDecimals", CONSTANTS_PRECISION);
	dissocRate->setAttributeInternal("stringDecimals", CONSTANTS_PRECISION);

	showWarningInUI = true;
}

void Reaction::controllableAdded(Controllable* c)
{
	if (c->parentContainer == reactants.get() || c->parentContainer == products.get())
	{
		TargetParameter* tp = (TargetParameter*)c;

		String prefix = c->parentContainer == reactants.get() ? "Reactant " : "Product ";
		tp->setNiceName(prefix + String(c->parentContainer->controllables.size()));
		tp->targetType = TargetParameter::CONTAINER;
		tp->maxDefaultSearchLevel = 0;
		tp->setRootContainer(EntityManager::getInstance());
	}
}

void Reaction::controllableRemoved(Controllable* c)
{
	String prefix = c->parentContainer == reactants.get() ? "Reactant " : "Product ";
	int index = 1;
	for (auto& controllable : c->parentContainer->controllables)
	{
		TargetParameter* tp = (TargetParameter*)controllable;
		tp->setNiceName(prefix + String(index++));
	}

	updateWarnAndRates();
}

void Reaction::addReactant(Entity* e)
{
	TargetParameter* tp = reactants->addTargetParameter("Reactant " + String(reactants->controllables.size() + 1), "Reactant " + String(reactants->controllables.size() + 1), EntityManager::getInstance());
	if (e != nullptr) tp->setValueFromTarget(e, false);
	tp->saveValueOnly = false;
	tp->isRemovableByUser = true;
}

void Reaction::addProduct(Entity* e)
{
	TargetParameter* tp = products->addTargetParameter("Product " + String(products->controllables.size() + 1), "Product " + String(products->controllables.size() + 1), EntityManager::getInstance());
	if (e != nullptr) tp->setValueFromTarget(e, false);
	tp->saveValueOnly = false;
	tp->isRemovableByUser = true;
}

Array<Entity*> Reaction::getAllReactants()
{
	Array<Entity*> result;
	for (auto& c : reactants->controllables)
	{
		result.add(((TargetParameter*)c)->getTargetContainerAs<Entity>());
	}
	return result;
}

Array<Entity*> Reaction::getAllProducts()
{
	Array<Entity*> result;
	for (auto& c : products->controllables)
	{
		result.add(((TargetParameter*)c)->getTargetContainerAs<Entity>());
	}
	return result;
}

void Reaction::clearReactants()
{
	while (!reactants->controllables.isEmpty())
		reactants->removeControllable(reactants->controllables.getLast());
}

void Reaction::clearProducts()
{
	while (!products->controllables.isEmpty())
		products->removeControllable(products->controllables.getLast());
}

void Reaction::autoRename()
{

	String newName;
	for (auto c : reactants->controllables)
	{
		if (newName.isNotEmpty())
			newName += "+";
		newName += c->niceName;
	}
	newName += "=";
	for (auto c : products->controllables)
	{
		if (newName.isNotEmpty())
			newName += "+";
		newName += c->niceName;
	}

	if (newName != niceName)
	{
		setNiceName(newName);
	}
}

void Reaction::inferEntities()
{
	if (isCurrentlyLoadingData)
		return;
	// only infer for empty reactions
	// if (!newReac)
	//   return;
	// DBG("Infering entities for reaction " + niceName);
	String name = niceName;
	int pos = name.indexOfChar('+');
	int pos2 = name.indexOfChar('=');

	if (pos > 0)
	{
		StringArray reactantNames;
		StringArray productNames;

		// Parse reactants and products from name
		if (pos2 > 0)
		{
			String reactantsPart = name.substring(0, pos2).trim();
			String productsPart = name.substring(pos2 + 1).trim();

			reactantNames.addTokens(reactantsPart, "+", "\"");
			productNames.addTokens(productsPart, "+", "\"");
		}
		else
		{
			NLOG("InferEntities", "Invalid reaction name format: " + name);
			return;
		}

		// clear reactants and products
		clearReactants();
		clearProducts();

		// Infer entities from reactant names
		for (int i = 0; i < reactantNames.size(); ++i)
		{
			String reactantName = reactantNames[i].trim();
			Entity* reactantEntity = EntityManager::getInstance()->getEntityFromName(reactantName);
			if (reactantEntity != nullptr)
			{
				addReactant(reactantEntity);
			}
			else
			{
				NLOG("InferEntities", "Could not infer reactant " + reactantName);
				return;
			}
		}

		// Infer entities from product names
		for (int i = 0; i < productNames.size(); ++i)
		{
			String productName = productNames[i].trim();
			Entity* productEntity = EntityManager::getInstance()->getEntityFromName(productName);
			if (productEntity != nullptr)
			{
				addProduct(productEntity);
			}
			else
			{
				NLOG("InferEntities", "Could not infer product " + productName);
				return;
			}
		}

		// Construct the new reaction name following the convention
		String newName;
		for (int i = 0; i < reactantNames.size(); ++i)
		{
			if (i > 0)
				newName += "+";
			newName += reactantNames[i];
		}
		newName += "=";
		for (int i = 0; i < productNames.size(); ++i)
		{
			if (i > 0)
				newName += "+";
			newName += productNames[i];
		}

		// Update the reaction name if it has changed
		if (newName != name)
		{
			niceName = newName;
		}
	}
}

void Reaction::onControllableFeedbackUpdateInternal(ControllableContainer* cc, Controllable* c)
{
	if (cc == reactants.get() || cc == products.get())
	{
		TargetParameter* tp = (TargetParameter*)c;
		if (Entity* e = dynamic_cast<Entity*>(tp->previousTargetContainer.get()))
		{

			// unregister old one
			unregisterLinkedInspectable(e);
			e->enabled->removeParameterListener(this);
			e->freeEnergy->removeParameterListener(this);
		}

		if (Entity* e = tp->getTargetContainerAs<Entity>())
		{

			registerLinkedInspectable(e);

			e->enabled->addParameterListener(this);
			e->freeEnergy->addParameterListener(this);
		}
	}
	updateWarnAndRates();
}

void Reaction::onExternalParameterValueChanged(Parameter* p)
{
	updateWarnAndRates();
}

void Reaction::afterLoadJSONDataInternal()
{
	updateWarnAndRates();
}

void Reaction::updateWarnAndRates()
{
	if (isCurrentlyLoadingData)
		return;
	bool someWarn = false;

	int disabledReactants = 0;
	int disabledProducts = 0;

	float energyLeft = 0;

	Array<Entity*> reactEntities = getAllReactants();

	for (auto e : reactEntities)
	{
		if (e == nullptr || !e->enabled->boolValue()) disabledReactants++;
		else energyLeft += e->freeEnergy->floatValue();
	}

	bool isSimulating = Simulation::getInstanceWithoutCreating() != nullptr && Simulation::getInstance()->state == Simulation::Simulating;
	if(isSimulating && disabledReactants > 0)
	{
		setWarningMessage("Some reactants are disabled or null", "DisabledReactants");
		someWarn = true;
	}
	else
		clearWarning("DisabledReactants");

	float energyRight = 0;

	Array<Entity*> productEntities = getAllProducts();
	for (auto e : productEntities)
	{
		if (e == nullptr || !e->enabled->boolValue()) disabledProducts++;
		else energyRight += e->freeEnergy->floatValue();
	}

	if (isSimulating && disabledProducts > 0)
	{
		setWarningMessage("Some products are disabled or null", "DisabledProducts");
		someWarn = true;
	}
	else
		clearWarning("DisabledProducts");

	if (someWarn)
		return;


	// total energy G* of the reaction: activation + max of GA+GB and GAB.
	float energyStar = energy->floatValue() + jmax(energyLeft, energyRight);
	// k1=exp(GA+GB-G*)
	assocRate->setValue(exp(energyLeft - energyStar));
	// k2=exp(GAB-G*)
	float newDissocRate = exp(energyRight - energyStar);
	dissocRate->setValue(newDissocRate);
}

bool Reaction::shouldIncludeInSimulation()
{
	if (!enabled->boolValue())
		return false;

	for (auto c : reactants->controllables)
	{
		Entity* e = ((TargetParameter*)c)->getTargetContainerAs<Entity>();
		if (e == NULL || !e->enabled->boolValue())
			return false;
	}

	for (auto c : products->controllables)
	{
		Entity* e = ((TargetParameter*)c)->getTargetContainerAs<Entity>();
		if (e == NULL || !e->enabled->boolValue())
			return false;
	}

	return true;
}

void Reaction::onContainerParameterChanged(Parameter* p)
{
	if (p == energy) updateWarnAndRates();
	if(simReac)
		simReac->updateFromReaction(this);
}