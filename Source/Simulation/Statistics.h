
#pragma once

#include "Simulation.h"

class Statistics : public Simulation::AsyncSimListener
{
public:
    juce_DeclareSingleton(Statistics, true);
    Statistics();
    ~Statistics();

    Simulation *simul;

    float epsilon = 0.0001f;

    int nbSim = 0;
    int maxNbSim = 10;

    Array<Array<float>> steadyStates;

    void genStartConcents();
    void launchSim();
    void computeStats();
    void printSteadyStates();
    void finishStats();
    void newMessage(const Simulation::SimulationEvent &e) override;
};