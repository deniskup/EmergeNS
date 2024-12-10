
#pragma once

#include "JuceHeader.h"
using namespace juce;

class SimReaction;
class Entity;

class Reaction : public BaseItem
{
public:
    Reaction(var params = var());
    Reaction(SimReaction*);

    ~Reaction();

    std::unique_ptr<ControllableContainer> reactants;
    std::unique_ptr<ControllableContainer> products;

    FloatParameter *energy;

    FloatParameter *assocRate;  // reactants to product
    FloatParameter *dissocRate; // product to reactants

    void clearItem();

    void addParams();

    void controllableAdded(Controllable *) override;

    void controllableRemoved(Controllable *) override;

    void addReactant(Entity *e);
    void addProduct(Entity *e);

	Array<Entity*> getAllReactants();
	Array<Entity*> getAllProducts();

    void clearReactants();
    void clearProducts();

    bool reached;   // can this reaction be built from primary entities ?

    void updateWarnAndRates();

    void autoRename();

    void inferEntities();

    bool shouldIncludeInSimulation();
    
    //"Internal" refers to the fact that the mother class has its own handling of the original function (before override), calling the internal in the middle of the code.
    void onControllableFeedbackUpdateInternal(ControllableContainer *,Controllable *) override;

    // External refers to the parameter not being a direct child of this container
    void onExternalParameterValueChanged(Parameter *p) override;


    void onContainerParameterChanged(Parameter *) override;

    void afterLoadJSONDataInternal() override;

    DECLARE_TYPE("Reaction");
};