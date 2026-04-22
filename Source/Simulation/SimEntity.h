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
#include "EntityManager.h"

class Entity;
class Space;
//using namespace juce;


class SimEntity
{
public:
    SimEntity(juce::var data); // import from JSON
    SimEntity(Entity* e);
    SimEntity(bool isPrimary, float concent, float cRate, float dRate, float freeEnergy);
    SimEntity(const SimEntity*);
  
    unique_ptr<SimEntity> clone() const; // cloning the sim entity

    void updateFromEntity(Entity* e);

    juce::var toJSONData();    // save to JSON

    ~SimEntity(); //delete and remove pointers to it

    bool constructionFailed = false;

    juce::String name;
    Entity* entity = nullptr; // sourceEntity

    juce::Colour color;
    bool primary;
    bool chemostat=false;
    int id = -1; // unique identifier
    //float concent;
    juce::Array<float> concent; // size = number of patches
    //float deterministicConcent;
    juce::Array<float> deterministicConcent;
    //float startConcent;
    juce::Array<float> startConcent;
    //float previousConcent;
    juce::Array<float> previousConcent;
    float creationRate; // could be heterogeneous in space. Left homogeneous for now
    float destructionRate; // same
    float freeEnergy;

    //juce::Array<float> concentHistory; // history of entity concentration
    // juce::Array<std::pair<int, float>> concentHistory; // history of entity [run ;concentration].

    //float change = 0.f; // variation of concentration in the last dt
    juce::Array<float> change = 0.f; // variation of concentration in the last dt
    //float deterministicChange = 0.f; // variation of concentration in the last dt (deterministic part only)
    juce::Array<float> deterministicChange = 0.f; // variation of concentration in the last dt (deterministic part only)

    bool reached; //is the entity reached from primary entities ?

    bool isolated = false; //true if the entity is not involved in any reaction

    //void importFromManual(); // retrieve info from pointer to Manual settings

    bool enabled = true;
    bool generatedFromUserList = true; // the entity has been generated from the user list
    bool toImport = false; // the corresponding entity has been modified

    int level;
    bool draw = true;

    Compo composition; // indexes are link to primary entities thanks to array primEnts

    int idSAT = 0; // identifier for SAT Solving

    void increase(int patchID, float incr);
    void deterministicIncrease(int patchID, float incr);
    void decrease(int patchID, float decr);
    void deterministicDecrease(int patchID, float decr);
    void refresh();

    void nameFromCompo();

    juce::String toString() const;
  
 /*
    // ASYNC
    class SimEntityEvent
    {
    public:
      enum Type
      {
        UPDATE_SIMENTITY,
      };

      SimEntityEvent(Type t) : type(t){};

      Type type;
      
    }; // end class SimEntityEvent


    QueuedNotifier<SimEntityEvent> simEntityNotifier;
    typedef QueuedNotifier<SimEntityEvent>::Listener AsyncSimEntityListener;

    void addAsyncSimEntityListener(AsyncSimEntityListener* newListener) { simEntityNotifier.addListener(newListener); }
    void addAsyncCoalescedSimEntityListener(AsyncSimEntityListener* newListener) { simEntityNotifier.addAsyncCoalescedListener(newListener); }
    void removeAsyncSimEntityListener(AsyncSimEntityListener* listener) { simEntityNotifier.removeListener(listener); }
*/
  

    JUCE_DECLARE_NON_COPYABLE_WITH_LEAK_DETECTOR(SimEntity);
};


typedef std::pair<SimEntity*, SimEntity*> Decomp;

class CompoDecomps
{
public:
    CompoDecomps(Compo comp, juce::Array<Decomp> ar) : compo(comp), decomps(ar) {}
    ~CompoDecomps()
    {
        decomps.clear();
    }
    Compo compo;
    juce::Array<Decomp> decomps;
    void add(SimEntity* e1, SimEntity* e2)
    {
        decomps.add(std::make_pair(e1, e2));
    }
};
