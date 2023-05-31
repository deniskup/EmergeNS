
#include "Statistics.h"
#include "Generation.h"
#include "Util.h"

juce_ImplementSingleton(Statistics)

Statistics::Statistics() : simul(Simulation::getInstance())
//    saveSimBT("Save"),
//    loadSimBT("Load")
// uiStep(1)
{
    simul->addAsyncSimulationListener(this);
}

Statistics::~Statistics()
{
    simul->removeAsyncSimulationListener(this);
    //  simul->removeAsyncContainerListener(this);
}

bool isClose(const Array<float> &a, const Array<float> &b, float epsilon)
{
    if (a.size() != b.size())
        return false;
    for (int i = 0; i < a.size(); i++)
    {
        if (abs(a[i] - b[i]) > epsilon)
            return false;
    }
    return true;
}

void Statistics::genStartConcents()
{
    // randomly choose starting concentrations

    const float initConcentBase = Generation::getInstance()->initConcent->x;
    const float initConcentVar = Generation::getInstance()->initConcent->y;

    // recall that energy of primary entities are normalized to 0

    for (auto &ent : simul->entities)
    {
        const float concent = jmax(0.f, initConcentBase + randFloat(-initConcentVar, initConcentVar));
        ent->startConcent = concent;
    }
}

void Statistics::launchSim()
{
    if (nbSim < maxNbSim)
    {
        // set initial values
        // launch simulation
        simul->start();
        nbSim++;
    }
    else
    {
        finishStats();
    }
}

void Statistics::computeStats()
{
    maxNbSim = Generation::getInstance()->numRuns->intValue();
    // we take 10 times the epsilon speed *dt.
    epsilon = 10 * simul->epsilonEq->floatValue() * simul->dt->floatValue();

    // processed so far
    nbSim = 0;

    steadyStates.clear();
}

void Statistics::newMessage(const Simulation::SimulationEvent &ev)
{
    switch (ev.type)
    {
    case Simulation::SimulationEvent::FINISHED:
    {
        // process result
        // check if already in steadyStates
        bool found = false;
        for (int i = 0; i < steadyStates.size(); i++)
        {
            if (isClose(steadyStates[i], ev.entityValues, epsilon))
            {
                found = true;
                break;
            }
        }
        if (!found)
        {
            steadyStates.add(ev.entityValues);
        }
        // launch next simulation
        launchSim();
    }
    break;
    }
}

void Statistics::finishStats()
{
    // display number of steady states
    LOG("Number of steady states: " << steadyStates.size());
}