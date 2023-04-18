
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

void cleanKissatOutput()
{
    ifstream infile("model.txt");
    ofstream outfile("model2.txt");
    string line;
    while (getline(infile, line))
    {
        if (line[0] == 'v' || line[0] == 's')
        {
            line.erase(0, 2);
            outfile << line << endl;
        }
        else
        {
            cout << "Error in Kissat output" << endl;
            break;
        }
    }
    infile.close();
    outfile.close();
    system("mv model2.txt model.txt");
}

// 0 for minisat, 1 for kissat
void findPAC(Simulation *simul, int numSolver)
{
    // clear PACs if some were computed
    simul->cycles.clear();

    // measure time
    uint32 startTime = Time::getMillisecondCounter();

    // declare SAT solvers
    SATSolver minisat("minisat", "minisat dimacs.txt model.txt >SATlog.txt", "SAT", false);
    SATSolver kissat("kissat", "~/Software/kissat/build/kissat -q dimacs.txt > model.txt", "SATISFIABLE", true);

    Array<SATSolver *> solvers = {&minisat, &kissat};

    SATSolver *solver = solvers[numSolver];

    LOG("Using solver: " + solver->name);

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
    for (auto &e : simul->entities)
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
    for (auto &r : simul->reactions)
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
    for (auto &r : simul->reactions)
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
            for (auto &r2 : simul->reactions)
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

    for (auto &r : simul->reactions)
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

        for (auto &r2 : simul->reactions)
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
        // an entity appears as reactant in at most one reaction
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
        // if the reaction is two to one (dir=0), the two reactants cannot be both in the pack:
        //  AND_j -reac[j] or dir[j] or not ent[reac1] or not ent[reac2]
        for (auto &r : simul->reactions)
        {
            j = r->idSAT;
            addClause({-reac[j], dir[j], -ent[r->reactant1->idSAT], -ent[r->reactant2->idSAT]});
        }
    }

    // in each selected reaction, at least one reactant and the product are selected
    for (auto &r : simul->reactions)
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

    // number of variables (and var max) without connexity
    const int nbVarBase = curvar;

    // write the dimacs, adding connexity with maximal distance to produce the autocatalyst, in order to find solutions in increasing size
    auto writeDimacs = [&](int distMax, string oldClauses, int nbOldClauses)
    {
        // add variables for connexity: dist[e,i,f] means that entity e produces entity f in at most i steps.

        // this is a naive encoding in Ent^2, we can do Ent*log(Ent)+Reac with bit encoding of distance
        int nbTotVar = nbVarBase; // restart curvar from beginning of connexity
        int nbTotClauses = nbOldClauses;

        int dist[Nent * (distMax + 1) * Nent];
        auto d2 = [&](int a, int b, int c)
        {
            return a * (distMax + 1) * Nent + b * Nent + c;
        };

        for (auto &e : simul->entities)
        {
            for (auto &f : simul->entities)
            {
                for (int d = 0; d <= distMax; d++)
                {
                    nbTotVar++;
                    dist[d2(e->idSAT, d, f->idSAT)] = nbTotVar;
                }
            }
        }

        // connexity clauses
        stringstream conClauses;
        // local function to add clause:
        auto addConClause = [&](Array<int> disjuncts)
        {
            for (int di : disjuncts)
            {
                conClauses << di << " ";
            }
            conClauses << "0" << endl;
            nbTotClauses++;
        };

        for (i = 0; i < Nent; i++)
        {

            for (j = 0; j < Nent; j++)
            {
                // 0 distance true iff i=j
                if (i == j)
                    addConClause({dist[d2(i, 0, i)], -ent[i]});
                else
                    addConClause({-dist[d2(i, 0, j)], -ent[i], -ent[j]});

                for (int d = 0; d <= distMax; d++)
                {
                    // dist=>ent
                    addConClause({-dist[d2(i, d, j)], ent[i]});
                    addConClause({-dist[d2(i, d, j)], ent[j]});
                }
            }
        }
        // advance(f,r,d,t)=isProd(f,r) and dist(f,d,t)
        // d<distMax is enough here since it is an advancement to d from d+1
        unordered_map<int, int> advance;
        auto d3 = [&](int a, int b, int c, int t)
        {
            return a * Nreac * distMax * Nent + b * distMax * Nent + c * Nent + t;
        };
        // initialisation
        for (auto &r : simul->reactions)
        {
            for (int d = 0; d < distMax; d++)
            {
                for (int t = 0; t < Nent; t++)
                {
                    nbTotVar++;
                    advance[d3(r->reactant1->idSAT, r->idSAT, d, t)] = nbTotVar;
                    nbTotVar++;
                    advance[d3(r->reactant2->idSAT, r->idSAT, d, t)] = nbTotVar;
                    nbTotVar++;
                    advance[d3(r->product->idSAT, r->idSAT, d, t)] = nbTotVar;
                }
            }
        }

        // clauses advance
        for (auto &r : simul->reactions)
        {
            int id1 = r->reactant1->idSAT;
            int id2 = r->reactant2->idSAT;
            int id3 = r->product->idSAT;
            Array<int> ids = {id1, id2, id3};

            int idr = r->idSAT;
            for (auto &f : ids)
            {

                for (int d = 0; d < distMax; d++)
                {
                    for (int t = 0; t < Nent; t++)
                    {
                        // advance(f,r,d)=isProd(f,r) and dist(f,d)
                        addConClause({-advance[d3(f, idr, d, t)], isProd[c2(f, idr)]});
                        addConClause({-advance[d3(f, idr, d, t)], dist[d2(f, d, t)]});
                        addConClause({advance[d3(f, idr, d, t)], -isProd[c2(f, idr)], -dist[d2(f, d, t)]});
                    }
                }
            }
        }

        // dist(e,d+1)=> dist(e,d) OR_(e->f) advance(f,r,d)
        for (int t = 0; t < Nent; t++)
        {
            for (int d = 0; d < distMax; d++)
            {
                for (auto &e : simul->entities)
                {

                    Array<int> distClause;
                    distClause.add(-dist[d2(e->idSAT, d + 1, t)]);
                    distClause.add(dist[d2(e->idSAT, d, t)]);
                    for (auto &r : simul->reactions)
                    {
                        int idr = r->idSAT;
                        if (!r->contains(e))
                            continue;
                        if (e == r->product)
                        {
                            distClause.add(advance[d3(r->reactant1->idSAT, idr, d, t)]);
                            distClause.add(advance[d3(r->reactant2->idSAT, idr, d, t)]);
                            continue;
                        }
                        // only remaining case: e is a reactant of r
                        distClause.add(advance[d3(r->product->idSAT, idr, d, t)]);
                    }
                    addConClause(distClause);
                }
            }
        }
        // finally, every chosen entity must satisfy distMax to every other
        for (int i = 0; i < Nent; i++)
        {
            for (int t = 0; t < Nent; t++)
            {
                addConClause({-ent[i], -ent[t], dist[d2(i, distMax, t)]});
            }
        }
        // write the dimacs
        ofstream dimacsStream;
        dimacsStream.open("dimacs.txt", ofstream::out | ofstream::trunc);
        dimacsStream << "p cnf " << nbTotVar << " " << nbTotClauses << endl;
        dimacsStream << oldClauses;
        dimacsStream << conClauses.str();

        // cout << "Dimacs generated with " << Nent << " entities and " << Nreac << " reactions\n";
        // cout << curvar << " variables and " << nbClauses << " clauses\n";
        dimacsStream.close();
    };

    int dmax_stop = 25;                // maximal dmax
    dmax_stop = jmin(dmax_stop, Nent); // put to Nent if bigger

    const int maxCycles = 200; // max number of cycles of some level before timeout

    simul->includeOnlyWithEntities = false; // forbid PAC with same entities but different reactions (to have less PACs)

    for (int dmax = 1; dmax < dmax_stop; dmax++)
    {
        writeDimacs(dmax, clauses.str(), nbClauses);
        bool sat = true;

        int nCycles;
        for (nCycles = 0; nCycles < maxCycles; nCycles++)
        {

            int retVal = system(solver->command.getCharPointer());
            if (retVal == -1)
            {
                LOGWARNING("SAT Solver command failed, exiting...");
                LOGWARNING("Command: " + solver->command);
                return;
            }
            if (solver->printsExtraString)

                cleanKissatOutput();

            ifstream sol_file("model.txt");
            string isSat;

            sol_file >> isSat;

            if (isSat != solver->satLine)
                break;

            int d;
            PAC *pac = new PAC();
            Array<int> newClause;
            int cycleSize = 0;
            for (auto &e : simul->entities)
            {
                sol_file >> d;
                if (d > 0)
                {
                    newClause.add(-d);
                    pac->entities.add(e);
                }
            }
            for (auto &r : simul->reactions)
            {
                // reaction
                int re;
                sol_file >> re;
                // pop direction
                sol_file >> d;
                if (re > 0)
                {
                    if (!simul->includeOnlyWithEntities)
                    {
                        newClause.add(-re);
                        newClause.add(-d);
                    }
                    pac->reacDirs.add(make_pair(r, (d > 0)));
                }
            }
            simul->addCycle(pac);
            // cout << pac->toString() << endl;
            if (pac->entities.size() != pac->reacDirs.size())
                cout << "Problem with PAC :" << pac->toString() << endl;
            addClause(newClause);
            writeDimacs(dmax, clauses.str(), nbClauses);
        }
        if (nCycles > 0)
            cout << nCycles << " PACs found for dmax=" << dmax << endl;
        else
            cout << ".";
        if (nCycles == maxCycles)
        {
            LOGWARNING(string(maxCycles) + " PACs reached for diameter " + string(dmax) + ", stop looking");
            break;
        }
    }
    cout << endl;
    simul->PACsGenerated = true;
    simul->updateParams();
    // simul->printPACs();

    // print execution time
    LOG("Execution time: " << String(Time::getMillisecondCounter() - startTime) << " ms");
}