
#include "GlobalActions.h"
#include "EntityManager.h"
#include "ReactionManager.h"

bool computeCompositions()
{
    int curId = 0;
    Array<Entity *> primaryEntities;
    for (auto &e : EntityManager::getInstance()->items)
    {
        e->compHasBeenSet = false;
        if (e->primary->boolValue())
        {
            e->id = curId;
            curId++;
            primaryEntities.add(e);
        }
    }
    for (auto &e : EntityManager::getInstance()->items)
    {
        e->composition.resize(curId);
        for (int prim = 0; prim < curId; prim++)
        {
            e->composition.set(prim, 0);
        }

        if (e->primary->boolValue())
        {
            e->composition.set(e->id, 1);
            e->compHasBeenSet = true;
        }
    }

    int nbReac = ReactionManager::getInstance()->items.size();
    bool progress = true;
    Array<Reaction *> reacToCheck;
    for (auto &r : ReactionManager::getInstance()->items)
        reacToCheck.add(r);
    while (!reacToCheck.isEmpty())
    {
        progress = false;
        for (int ir = 0; ir < reacToCheck.size(); ir++)
        {
            Reaction *r = reacToCheck[ir];
            Entity *r1 = (Entity *)r->reactant1;
            Entity *r2 = (Entity *)r->reactant2;
            Entity *p = (Entity *)r->product;

            if (r1->compHasBeenSet && r2->compHasBeenSet && !p->compHasBeenSet)
            {
                progress = true;
                for (int prim = 0; prim < curId; prim++)
                {
                    p->composition.set(prim, r1->composition[prim] + r2->composition[prim]);
                }
                reacToCheck.remove(ir);
                DBG("Reaction " + r->niceName + " used");
            }
            else if (r1->compHasBeenSet && r2->compHasBeenSet && p->compHasBeenSet)
            {
                progress = true;
                for (int prim = 0; prim < curId; prim++)
                {
                    if (p->composition[prim] != r1->composition[prim] + r2->composition[prim])
                    {
                        AlertWindow::showMessageBoxAsync(AlertWindow::AlertIconType::WarningIcon, "Unbalanced reactions", "Reaction " + r->niceName + " does not preserve primary entities, unable to compute compositions", "OK");
                        return false;
                    }
                }
                reacToCheck.remove(ir);
                DBG("Reaction " + r->niceName + " OK");
            }
        }
        if (!progress)
            break;
    }
    if (!reacToCheck.isEmpty())
    {
        AlertWindow::showMessageBoxAsync(AlertWindow::AlertIconType::WarningIcon, "Unverified reactions", "Reaction " + reacToCheck[0]->niceName + " could not be verified", "OK");
        return false;
    }
    // optional: check that composition of everyone has been done
    /*for (auto &e:EntityManager::getInstance()->items){
        if(!e->compHasBeenSet){
            AlertWindow::showMessageBoxAsync(AlertWindow::AlertIconType::WarningIcon, "Entity not formed from primaries", "Entity " + e->niceName + " cannot be formed.", "OK");
        }
    }
    */
    return true;
}

void normEnergies()
{
    if (!computeCompositions())
        return;
    // we must know the composition in terms of primary entities
}