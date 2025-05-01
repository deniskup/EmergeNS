/*
  ==============================================================================

	SimulationHelpers.h
	Created: 29 Sep 2024 11:28:42am
	Author:  bkupe

  ==============================================================================
*/

#pragma once
#include <JuceHeader.h>
using namespace juce;
using namespace std;

class SimEntity;
class PAC;
typedef Array<int> Compo;

class SimulationHelpers
{
public:
	static var color2JSON(Colour col)
	{
		var data = new DynamicObject();
		data.getDynamicObject()->setProperty("H", col.getHue());
		data.getDynamicObject()->setProperty("S", col.getSaturation());
		data.getDynamicObject()->setProperty("B", col.getBrightness());
		data.getDynamicObject()->setProperty("A", col.getAlpha());
		return data;
	}

	static Colour JSON2Color(var data)
	{
		return Colour::fromHSV(data["H"], data["S"], data["B"], data["A"]);
	}
};


class ConcentrationSnapshot // concentration snapshot recorded in a single patch and for a single run. Should rename class name
{
public:
  ConcentrationSnapshot() {};
  std::map<SimEntity*, float> conc;
  int runID = 0;
  int patchID = 0;
  int step;
  
  
};


class RACSnapshot
{
public:
	  public:
  //RACSnapshot(float r, Array<float> f, Array<float> pp, Array<float> pm, Array<float> sp) : rac(r), flows(f), posSpecificities(pp), negSpecificities(pm), specificity(sp)
  RACSnapshot(float r, Array<float> f) : rac(r), flows(f)
    {}
  int runID = 0;
  int patchID = 0;
  int racID;
  int step;
  float rac;
  Array<float> flows;
  //Array<float> posSpecificities;
  //Array<float> negSpecificities;
  //Array<float> specificity;
};

class RACHist // RAC dynamics recorded in a single patch and for a single run
{
public:
	RACHist() {}
	RACHist(Array<SimEntity*> e) { ents = e; }
	RACHist(Array<SimEntity*> e, float s) { ents = e; pacScore = s; }
	OwnedArray<RACSnapshot> hist;
	Array<SimEntity*> ents;
	float pacScore = 0.;
  bool wasRAC = false;
  //int runID = 0;
  //int patchID = 0;
  
};



class DynamicsHistory
{
public:
  DynamicsHistory(){};
  ~DynamicsHistory(){};

  Array<ConcentrationSnapshot> concentHistory; // concentration history
  Array<RACSnapshot> racHistory; // RAC history
  std::map<PAC*, bool> wasRAC; // true if the PAC is on at some point "on" in the simulation (for drawing)
  
  
  ConcentrationSnapshot getLastConcentrationSnapshot()
  {
    return concentHistory.getUnchecked(concentHistory.size()-1);
  }
  
  Array<ConcentrationSnapshot> getConcentrationDynamicsForStep(int _stepid)
  {
    Array<ConcentrationSnapshot> output;
    for (auto & cs : concentHistory)
    {
      if (cs.runID == _stepid)
        output.add(cs);
    }
    return output;
  }
  
  Array<ConcentrationSnapshot> getConcentrationDynamicsForRun(int _runid)
  {
    Array<ConcentrationSnapshot> output;
    for (auto & cs : concentHistory)
    {
      if (cs.runID == _runid)
        output.add(cs);
    }
    return output;
  }
  
  Array<ConcentrationSnapshot> getConcentrationDynamicsForPatch(int _pid)
  {
    Array<ConcentrationSnapshot> output;
    for (auto & cs : concentHistory)
    {
      if (cs.patchID == _pid)
        output.add(cs);
    }
    return output;
  }
  
  Array<ConcentrationSnapshot> getConcentrationDynamicsForRunAndPatch(int _runid, int _pid)
  {
    Array<ConcentrationSnapshot> output;
    for (auto & cs : concentHistory)
    {
      if (cs.runID == _runid && cs.patchID == _pid)
        output.add(cs);
    }
    return output;
  }
  
  // getter of RAC snapshots
  
  RACSnapshot getLastRACSnapshot()
  {
    return racHistory.getUnchecked(racHistory.size()-1);
  }
  
  RACSnapshot getLastRACSnapshotInPatch(int pid)
  {
    for (int k = racHistory.size()-1; k>=0; k--)
    {
      if (racHistory.getUnchecked(k).patchID == pid)
        return racHistory.getUnchecked(k);
    }
  }
  
  Array<RACSnapshot> getRACDynamicsForRun(int _runid)
  {
    Array<RACSnapshot> output;
    for (auto & rs : racHistory)
    {
      if (rs.runID == _runid)
        output.add(rs);
    }
    return output;
  }
  
  Array<RACSnapshot> getRACDynamicsForPatch(int _pid)
  {
    Array<RACSnapshot> output;
    for (auto & rs : racHistory)
    {
      if (rs.patchID == _pid)
        output.add(rs);
    }
    return output;
  }
  
  Array<RACSnapshot> getRACDynamicsForRunAndPatch(int _runid, int _pid)
  {
    Array<RACSnapshot> output;
    for (auto & rs : racHistory)
    {
      if (rs.runID == _runid && rs.patchID == _pid)
        output.add(rs);
    }
    return output;
  }
  
  

};
