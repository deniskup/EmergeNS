
#pragma once

#include "Simulation.h"

class Statistics :   public Simulation::AsyncSimListener
{
public:
    Statistics();
    ~Statistics();

    Simulation *simul;

    float epsilon = 0.0001f;

    int nbSim=0;
    int maxNbSim=10;

    Array<Array<float>> steadyStates;

    void launchSim();

    void computeStats(int nbIterations);

    void finishStats();

    void newMessage(const Simulation::SimulationEvent &e) override;

};