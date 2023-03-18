
#include "GlobalActions.h"
#include "EntityManager.h"
#include "ReactionManager.h"
#include "Simulation.h"
#include <fstream>
#include <sstream>

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
                        AlertWindow::showMessageBoxAsync(AlertWindow::AlertIconType::WarningIcon, "Unbalanced reactions", "Reaction " + r->niceName + " does not preserve primary entities, unable to compute compositions", "OK");
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
        AlertWindow::showMessageBoxAsync(AlertWindow::AlertIconType::WarningIcon, "Unverified reactions", "Reaction " + reacToCheck[0]->niceName + " could not be verified", "OK");
        return -1;
    }
    // optional: check that composition of everyone has been done
    /*for (auto &e:EntityManager::getInstance()->items){
        if(!e->compHasBeenSet){
            AlertWindow::showMessageBoxAsync(AlertWindow::AlertIconType::WarningIcon, "Entity not formed from primaries", "Entity " + e->niceName + " cannot be formed.", "OK");
        }
    }
    */
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

void findPAC(Simulation *simul)
{

    // open file
    stringstream clauses;

    // for now to Dimacs, to integrate with Kissat later

    // a PAC is a subset of n reactions and n entities, such that
    //  -every entity is reactant of exactly one of the reactions, and product of at least one
    //  -there is an entity produced twice
    int nbclauses = 0;

    int Nent = simul->entities.size();
    int Nreac = simul->reactions.size();

    int curvar = 0; // number of current variable
    // if entity i is taken in the cycle C
    int ent[Nent];
    int i = 0, j, k;
    for (auto e : simul->entities)
    {
        curvar++;
        ent[i] = curvar;
        e->idSAT = i;
        i++;
    }

    // if reaction j is taken in the cycle C
    int reac[Nreac];
    // for taken reactions: which direction is used. 0 is reactants->product and 1 is product->reactants
    int dir[Nreac];
    j = 0;
    for (auto r : simul->reactions)
    {
        curvar++;
        reac[j] = curvar;
        r->idSAT = j;
        curvar++;
        dir[j] = curvar;
        j++;
    }

    // is e reactant of r according to the chosen direction of r ? we also want the reaction to exist
    int isReac[Nent][Nreac];
    int isProd[Nent][Nreac];
    int isProds[Nent][Nreac][Nreac]; // for this one we also ask the entity to exist as well
    for (i = 0; i < Nent; i++)
    {
        for (j = 0; j < Nreac; j++)
        {
            curvar++;
            isReac[i][j] = curvar;

            curvar++;
            isProd[i][j] = curvar;

            for (k = j; k < Nreac; k++)
            {
                curvar++;
                isProds[i][j][k] = curvar;
            }
        }
    }

    // correctness of isReac: either e is a reactant and dir=0, or e is a product and dir=1. Also reac[j] has to be true
    for (auto e : simul->entities)
    {
        i = e->idSAT;
        for (auto r : simul->reactions)
        {
            j = r->idSAT;
            // isReac true implies reac chosen, and isProds implies entity exists
            //  not isReac[i][j] OR reac[j]
            clauses << -isReac[i][j] << " " << reac[j] << " 0" << endl;
            nbclauses++;
            // not isProd[i][j] OR reac[j]
            clauses << -isProd[i][j] << " " << reac[j] << " 0" << endl;
            nbclauses++;
            // not isProds[i][j][j] OR ent[i]
            clauses << -isProds[i][j][j] << " " << ent[i] << " 0" << endl;
            nbclauses++;

            if (r->reactant1->idSAT == i || r->reactant2->idSAT == i)
            {
                // (not isReac[i][j]) OR not dir[j]
                clauses << -isReac[i][j] << " " << -dir[j] << " 0" << endl;
                nbclauses++;
                // isReac[i][j] OR dir[j] OR not reac[j]
                clauses << isReac[i][j] << " " << dir[j] << " " << -reac[j] << " 0" << endl;
                nbclauses++;

                // (not isProd[i][j]) OR dir[j]
                clauses << -isProd[i][j] << " " << dir[j] << " 0" << endl;
                nbclauses++;
                // isProd[i][j] OR not dir[j] OR not reac[j]
                clauses << isProd[i][j] << " " << -dir[j] << " " << -reac[j] << " 0" << endl;
                nbclauses++;

                // double product
                if (r->reactant1->idSAT == i && r->reactant2->idSAT == i)
                {

                    // isProds[i][j][j] OR not dir[j] Or not reac[j] OR not ent[i]
                    clauses << isProds[i][j][j] << " " << -dir[j] << " " << -reac[j] << " " << -ent[i] << " 0" << endl;
                    nbclauses++;
                }
                else
                {
                    // not isProds[i][j][j]
                    clauses << -isProds[i][j][j] << " 0" << endl;
                    nbclauses++;
                }
            }
            else if (r->product->idSAT == i)
            {
                // (not isReac[i][j]) OR dir[j]
                clauses << -isReac[i][j] << " " << dir[j] << " 0" << endl;
                nbclauses++;
                // isReac[i][j] OR not dir[j] OR not reac[j]
                clauses << isReac[i][j] << " " << -dir[j] << " " << -reac[j] << " 0" << endl;
                nbclauses++;
                // (not isProd[i][j]) OR not dir[j]
                clauses << -isProd[i][j] << " " << -dir[j] << " 0" << endl;
                nbclauses++;
                // isProd[i][j] OR dir[j] OR not reac[j]
                clauses << isProd[i][j] << " " << dir[j] << " " << -reac[j] << " 0" << endl;
                nbclauses++;

                // not isProds[i][j][j]
                clauses << -isProds[i][j][j] << " 0" << endl;
                nbclauses++;
            }
            else
            {
                // not isReac[i][j]
                clauses << -isReac[i][j] << " 0" << endl;
                nbclauses++;
                // not isProd[i][j]
                clauses << -isProd[i][j] << " 0" << endl;
                nbclauses++;
                // not isProds[i][j][j]
                clauses << -isProds[i][j][j] << " 0" << endl;
                nbclauses++;
            }
            for (k = j + 1; k < Nreac; k++)
            {
                // not isProds[i][j][k] OR ent[i]
                clauses << -isProds[i][j][k] << " " << ent[i] << " 0" << endl;
                nbclauses++;
                // not isProds[i][j][k] OR isProd[i][j]
                clauses << -isProds[i][j][k] << " " << isProd[i][j] << " 0" << endl;
                nbclauses++;
                // not isProds[i][j][k] OR isProd[i][k]
                clauses << -isProds[i][j][k] << " " << isProd[i][k] << " 0" << endl;
                nbclauses++;
                // isProds[i][j][k] OR not isProd[i][j] OR not isProd[i][k] OR not ent[i]
                clauses << isProds[i][j][k] << " " << -isProd[i][j] << " " << -isProd[i][k] << " " << -ent[i] << " 0" << endl;
                nbclauses++;
            }
        }
    }

    // each entity appears exactly once as reactant
    for (i = 0; i < Nent; i++)
    {
        // e not chosen or appears as reactant of r
        // not ent[i] or OR_j isReac[i][j]
        clauses << -ent[i];
        for (j = 0; j < Nreac; j++)
            clauses << " " << isReac[i][j];
        clauses << " 0" << endl;
        nbclauses++;
        // not ent[i] or OR_j isProd[i][j]
        clauses << -ent[i];
        for (j = 0; j < Nreac; j++)
            clauses << " " << isProd[i][j];
        clauses << " 0" << endl;
        nbclauses++;
        // exactly one reactant
        // AND_{j<k} not ent[i] or not isReac[i][j] or not isReac[i][k]
        for (j = 0; j < Nreac; j++)
        {
            for (int k = j + 1; k < Nreac; k++)
            {
                clauses << -ent[i] << " " << -isReac[i][j] << " " << -isReac[i][k] << " 0" << endl;
                nbclauses++;
            }
        }
    }

    // in each selected reaction, at least one reactant and the product are selected
    for (auto r : simul->reactions)
    {
        j = r->idSAT;
        clauses << -reac[j] << " " << ent[r->reactant1->idSAT]<< " "<< ent[r->reactant2->idSAT]<< " 0"<<endl;
        nbclauses++;
        clauses << -reac[j] << " " << ent[r->product->idSAT]<< " 0"<<endl;
        nbclauses++;
    }

    // one entity is produced twice
    // OR_i OR_{j<=k} isProds[i][j][k]
    for (i = 0; i < Nent; i++)
    {
        for (j = 0; j < Nreac; j++)
        {
            for (int k = j; k < Nreac; k++)
            {
                clauses << isProds[i][j][k] << " ";
            }
        }
    }
    clauses << "0" << endl;
    nbclauses++;

    ofstream dimacsStream;
    dimacsStream.open("dimacs.txt", ofstream::out | ofstream::trunc);

    dimacsStream << "p cnf " << curvar << " " << nbclauses << endl;
    dimacsStream << clauses.str();
    cout << "Dimacs generated with " << Nent << " entities and " << Nreac << " reactions\n";
    cout << curvar << " variables and " << nbclauses << " clauses\n";
}