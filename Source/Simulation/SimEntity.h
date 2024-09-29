/*
  ==============================================================================

    SimEntity.h
    Created: 29 Sep 2024 11:09:38am
    Author:  bkupe

  ==============================================================================
*/

#pragma once

#include "JuceHeader.h"
#include "SimulationHelpers.h"

class Entity;
using namespace juce;


class SimEntity
{
public:
    SimEntity(var data); // import from JSON
    SimEntity(Entity* e);
    SimEntity(bool isPrimary, float concent, float cRate, float dRate, float freeEnergy);


    var toJSONData();    // save to JSON

    ~SimEntity(); //delete and remove pointers to it

    bool constructionFailed = false;

    String name;
    Entity* entity = nullptr; // sourceEntity

    Colour color;
    bool primary;
    int id = -1; // unique identifier
    float concent;
    float startConcent;
    float previousConcent;
    float creationRate;
    float destructionRate;
    float freeEnergy;

    Array<float> concentHistory; // history of entity concentration 

    float change = 0.f; // variation of concentration in the last dt

    bool reached; //is the entity reached from primary entities ?

    bool isolated = false; //true if the entity is not involved in any reaction

    //void importFromManual(); // retrieve info from pointer to Manual settings

    bool enabled = true;
    bool toImport = false; // the corresponding entity has been modified

    int level;
    bool draw = true;

    Compo composition; // indexes are link to primary entities thanks to array primEnts

    int idSAT = 0; // identifier for SAT Solving

    void increase(float incr);
    void decrease(float decr);
    void refresh();
    void nameFromCompo();

    String toString() const;

    JUCE_DECLARE_NON_COPYABLE_WITH_LEAK_DETECTOR(SimEntity);
};


typedef std::pair<SimEntity*, SimEntity*> Decomp;

class CompoDecomps
{
public:
    CompoDecomps(Compo comp, Array<Decomp> ar) : compo(comp), decomps(ar) {}
    ~CompoDecomps()
    {
        decomps.clear();
    }
    Compo compo;
    Array<Decomp> decomps;
    void add(SimEntity* e1, SimEntity* e2)
    {
        decomps.add(std::make_pair(e1, e2));
    }
};
