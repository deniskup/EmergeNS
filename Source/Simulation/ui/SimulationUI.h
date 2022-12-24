
#pragma once

#include "../Simulation.h"

class SimulationUI :
    public ShapeShifterContentComponent
{
public:
    SimulationUI();
    ~SimulationUI();

    static SimulationUI* create(const String& name) { return new SimulationUI(); }

};