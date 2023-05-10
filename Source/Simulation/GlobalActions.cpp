
#include "GlobalActions.h"
#include "EntityManager.h"
#include "ReactionManager.h"
#include "Simulation.h"
#include <fstream>
#include <sstream>
#include <unordered_map>

#define DBOOL(V) (V ? "true" : "false")




int computeCompositions()
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

    //int nbReac = ReactionManager::getInstance()->items.size();
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
            Entity *r1 = (Entity *)r->linkedR1.get();
            Entity *r2 = (Entity *)r->linkedR2.get();
            Entity *p = (Entity *)r->linkedP.get();
            DBG("Looking at " + r->niceName);
            DBG(DBOOL(r2->compHasBeenSet) << " & " << DBOOL(r2->compHasBeenSet) << " & " << DBOOL(p->compHasBeenSet));
            if (r1->compHasBeenSet && r2->compHasBeenSet && !p->compHasBeenSet)
            {
                progress = true;
                for (int prim = 0; prim < curId; prim++)
                {
                    p->composition.set(prim, r1->composition[prim] + r2->composition[prim]);
                }
                p->compHasBeenSet = true;
                reacToCheck.remove(ir);
                DBG("Reaction " + r->niceName + " used");
                break;
            }
            else if (r1->compHasBeenSet && r2->compHasBeenSet && p->compHasBeenSet)
            {
                progress = true;
                for (int prim = 0; prim < curId; prim++)
                {
                    if (p->composition[prim] != r1->composition[prim] + r2->composition[prim])
                    {
                        //LOGWARNING("Unbalanced reactions", "Reaction " + r->niceName + " does not preserve primary entities, unable to compute compositions");
                        return -1;
                    }
                }
                reacToCheck.remove(ir);
                DBG("Reaction " + r->niceName + " OK");
                break;
            }
        }
        if (!progress)
            break;
    }
    if (!reacToCheck.isEmpty())
    {
        //LOGWARNING("Reaction " + reacToCheck[0]->niceName + " could not be verified");
        return -1;
    }
    // optional: check that composition of everyone has been done
    /*for (auto &e:EntityManager::getInstance()->items){
        if(!e->compHasBeenSet){
            AlertWindow::showMessageBoxAsync(AlertWindow::AlertIconType::WarningIcon, "Entity not formed from primaries", "Entity " + e->niceName + " cannot be formed.", "OK");
        }
    }
    */

   //compute levels based on compositions
    for (auto &e : EntityManager::getInstance()->items)
    {
        e->level = 0;
        for (int prim = 0; prim < curId; prim++)
        {
            e->level+=e->composition[prim];
        }
    }

    return curId;
}

void normEnergies()
{
    int nbPrim = computeCompositions();
    if (nbPrim == -1)
        return;
    // Now that we know the composition, it suffices to perform the algorithm
    Array<float> primEnergies;
    primEnergies.resize(nbPrim);
    for (auto &e : EntityManager::getInstance()->items)
    {
        if (e->primary->boolValue())
        {
            primEnergies.set(e->id, e->freeEnergy->floatValue());
        }
    }
    for (auto &e : EntityManager::getInstance()->items)
    {
        float energ = e->freeEnergy->floatValue();
        for (int i = 0; i < nbPrim; i++)
        {
            energ -= e->composition[i] * primEnergies[i];
        }
        e->freeEnergy->setValue(energ);
    }
}

