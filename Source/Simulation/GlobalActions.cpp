
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

    ofstream varfile;
    varfile.open("vars.txt", ofstream::out | ofstream::trunc);
    // for now to Dimacs, to integrate with Kissat later

    // a PAC is a subset of n reactions and n entities, such that
    //  -every entity is reactant of exactly one of the reactions, and product of at least one
    //  -there is an entity produced twice
    int nbClauses = 0;

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
        varfile << "Ent " << e->name << ": " << curvar << endl;
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
        varfile << "Reac " << r->reactant1->name << "+" << r->reactant2->name << " : " << curvar << endl;
        r->idSAT = j;
        curvar++;
        dir[j] = curvar;
        varfile << "Dir " << curvar << endl;
        j++;
    }

    // TODO optimize: only put the variables that have a chance to be true, ie isReac[c2(i,j)] exists only if entity i appears in reaction j.
    //  use Hashtables instead of double/triple arrays

    // compress 2 indices (Nent,Nreac) into one
    auto c2 = [&](int a, int b)
    {
        return a * Nreac + b;
    };
    // compress 3 indices (Nent,Nreac,Nreac) into one
    auto c3 = [&](int a, int b, int c)
    {
        return a * Nreac * Nreac + b * Nreac + c;
    };

    // add only possible ones
    unordered_map<int, int> isReac;
    unordered_map<int, int> isProd;
    unordered_map<int, int> isProds;
    for (auto r : simul->reactions)
    {
        int idr = r->idSAT;
        // ids of entities involved
        int id1 = r->reactant1->idSAT;
        int id2 = r->reactant2->idSAT;
        int id3 = r->product->idSAT;
        Array<int> ids = {id1, id2, id3};

        // possibility of double product
        if (id1 == id2)
        {
            curvar++;
            isProds[c3(id1, idr, idr)] = curvar;
            varfile << "is2Prods " << r->reactant1->name << " : " << curvar << endl;
        }
        for (auto i : ids)
        {
            curvar++;
            isReac[c2(i, idr)] = curvar;
            varfile << "isReac " << r->reactant1->name << " with " << r->reactant2->name << " : " << curvar << endl;
            curvar++;
            isProd[c2(i, idr)] = curvar;
            varfile << "isProd " << r->reactant1->name << " from " << r->reactant1->name << " : " << curvar << endl;
            for (auto r2 : simul->reactions)
            {
                if (r2->idSAT <= idr)
                    continue;
                if (i == r2->reactant1->idSAT || i == r2->reactant2->idSAT || i == r2->product->idSAT)
                {

                    curvar++;
                    isProds[c3(i, idr, r2->idSAT)] = curvar;
                    varfile << "isProds " << ent[i] << " from " << r->reactant1->name << "+" << r->reactant2->name << " and " << r2->reactant1->name << "+" << r2->reactant2->name << " : " << curvar << endl;
                }
            }
        }
    }

    // local function to add clause:
    auto addClause = [&](Array<int> disjuncts)
    {
        for (int d : disjuncts)
        {
            clauses << d << " ";
        }
        clauses << "0" << endl;
        nbClauses++;
    };

    // correctness of isReac: either e is a reactant and dir=0, or e is a product and dir=1. Also reac[j] has to be true
    // for isReac to be true we also need to verify that the other reactant is different, we do not want to allow A+A->AA in this direction

    for (auto r : simul->reactions)
    {
        j = r->idSAT;

        // isReac true implies reac chosen, and isProds c3(i,l,s) entity exists
        //  not isReac[c2(i,j)] OR reac[j]
        int id1 = r->reactant1->idSAT;
        int id2 = r->reactant2->idSAT;
        int id3 = r->product->idSAT;
        Array<int> ids = {id1, id2, id3};
        Array<int> idleft = {id1, id2};

        if (id1 == id2)
        {
            int ijj = c3(id1, j, j);
            int ij = c2(id1, j);
            // isProds <=> dir[j] and reac[j] and ent[i]
            addClause({isProds[ijj], -dir[j], -reac[j], -ent[id1]});
            addClause({-isProds[ijj], ent[id1]});
            addClause({-isProds[ijj], dir[j]});
            addClause({-isProds[ijj], reac[j]});
            // isReac false if two reactants are the same
            addClause({-isReac[ij]});
            // product normal (even if useless normally, Prods takes care of it)
            addClause({-isProd[ij], reac[j]});
            addClause({-isProd[ij], dir[j]});
            addClause({isProd[ij], -dir[j], -reac[j]});
        }
        else
        { // if different, we can put conditions on both isReac
            for (auto i : idleft)
            {
                int ij = c2(i, j);
                // isProd <=> dir and reac
                addClause({-isProd[ij], reac[j]});
                addClause({-isProd[ij], dir[j]});
                addClause({isProd[ij], -dir[j], -reac[j]});

                // isReac <=> -dir and reac
                addClause({-isReac[ij], reac[j]});
                addClause({-isReac[ij], -dir[j]});
                addClause({isReac[ij], dir[j], -reac[j]});
            }
        }
        // for the solitary side
        //  isReac <=> dir and reac
        int ij = c2(id3, j);
        addClause({-isReac[ij], reac[j]});
        addClause({-isReac[ij], dir[j]});
        addClause({isReac[ij], -dir[j], -reac[j]});
        // isProd <=> -dir and reac
        addClause({-isProd[ij], reac[j]});
        addClause({-isProd[ij], -dir[j]});
        addClause({isProd[ij], dir[j], -reac[j]});

        for (auto r2 : simul->reactions)
        {
            int k = r2->idSAT;
            if (k <= j)
                continue;
            for (auto i : ids)
            {
                if (i == r2->reactant1->idSAT || i == r2->reactant2->idSAT || i == r2->product->idSAT)
                {
                    int ijk = c3(i, j, k);
                    // isProds[c3(i,j,k)]<=> ent[i] and isProd[c2(i,j)] and isProd[c2(i,
                    addClause({-isProds[ijk], ent[i]});
                    addClause({-isProds[ijk], isProd[c2(i, j)]});
                    addClause({-isProds[ijk], isProd[c2(i, k)]});
                    addClause({isProds[ijk], -isProd[c2(i, j)], -isProd[c2(i, k)], -ent[i]});
                }
            }
        }
    }

    // each entity appears exactly once as reactant
    for (i = 0; i < Nent; i++)
    {
        // e not chosen or appears as reactant of r
        // not ent[i] or OR_j isReac[c2(i,j)]
        clauses << -ent[i];
        for (j = 0; j < Nreac; j++)
        {
            auto it = isReac.find(c2(i, j));
            if (it != isReac.end())
                clauses << " " << it->second;
        }
        clauses << " 0" << endl;
        nbClauses++;
        // not ent[i] or OR_j isProd[c2(i,j)]
        clauses << -ent[i];
        for (j = 0; j < Nreac; j++)
        {
            auto it = isProd.find(c2(i, j));
            if (it != isProd.end())
                clauses << " " << it->second;
        }
        clauses << " 0" << endl;
        nbClauses++;
        // exactly one reactant
        // AND_{j<k} not ent[i] or not isReac[c2(i,j)] or not isReac[c2(i,k)]
        for (j = 0; j < Nreac; j++)
        {
            for (int k = j + 1; k < Nreac; k++)
            {
                auto it1 = isReac.find(c2(i, j));
                if (it1 == isReac.end())
                    continue;
                auto it2 = isReac.find(c2(i, k));
                if (it2 == isReac.end())
                    continue;

                addClause({-ent[i], -it1->second, -it2->second});
            }
        }
    }

    // in each selected reaction, at least one reactant and the product are selected
    for (auto r : simul->reactions)
    {
        j = r->idSAT;
        addClause({-reac[j], ent[r->reactant1->idSAT], ent[r->reactant2->idSAT]});
        addClause({-reac[j], ent[r->product->idSAT]});
    }

    // one entity is produced twice
    // OR_i OR_{j<=k} isProds[c3(i,j,k)]

    for (auto it : isProds)
    {
        clauses << it.second << " ";
    }
    clauses << "0" << endl;
    nbClauses++;

    ofstream dimacsStream;

    auto writeDimacs = [&]()
    {
        dimacsStream.open("dimacs.txt", ofstream::out | ofstream::trunc);
        dimacsStream << "p cnf " << curvar << " " << nbClauses << endl;
        dimacsStream << clauses.str();
        //cout << "Dimacs generated with " << Nent << " entities and " << Nreac << " reactions\n";
        //cout << curvar << " variables and " << nbClauses << " clauses\n";
        dimacsStream.close();
    };

    writeDimacs();

    bool sat = true;
    const int maxCycles = 100;
    int nCycles;
    for (nCycles = 0; nCycles < maxCycles; nCycles++)
    {
        system("minisat dimacs.txt model.txt >err");
        ifstream sol_file("model.txt");
        string isSat;
        sol_file >> isSat;
        if (isSat != "SAT")
            break;
        int d;
        Array<int> newClause;
        int cycleSize = 0;
        for (auto e : simul->entities)
        {
            sol_file >> d;
            if (d > 0)
            {
                newClause.add(-d);
                cout <<e->name<<" ";
                cycleSize++;

            }
        }

        cout <<endl;
        for (auto r : simul->reactions)
        {
            // reaction
            sol_file >> d;
            if (d > 0)
            {
                newClause.add(-d);
            }
            // pop direction
            sol_file >> d;
        }
        addClause(newClause);
        writeDimacs();
    }
    cout << nCycles << " cycles trouvés" << endl;
}