/*
  ==============================================================================

	SimulationHelpers.h
	Created: 29 Sep 2024 11:28:42am
	Author:  bkupe

  ==============================================================================
*/

#pragma once
#include <JuceHeader.h>
//using namespace juce;
using namespace std;

class SimEntity;
class PAC;
typedef juce::Array<int> Compo;

class SimulationHelpers
{
public:
	static juce::var color2JSON(juce::Colour col)
	{
		juce::var data = new juce::DynamicObject();
		data.getDynamicObject()->setProperty("H", col.getHue());
		data.getDynamicObject()->setProperty("S", col.getSaturation());
		data.getDynamicObject()->setProperty("B", col.getBrightness());
		data.getDynamicObject()->setProperty("A", col.getAlpha());
		return data;
	}

	static juce::Colour JSON2Color(juce::var data)
	{
		return juce::Colour::fromHSV(data["H"], data["S"], data["B"], data["A"]);
	}
};





/*
 This type represents concentrations of entities over all the space grid at a given time
 The map is defined as follow :
 map< pair<patchID, entID>, concentration >
 By default this map will be sorted first by ascending patchID, secondaly by ascending entID.
*/
typedef map<pair<int, int>, float> ConcentrationGrid;



class ConcentrationSnapshot // concentration snapshot recorded for a single run.
{
public:
  ConcentrationSnapshot() {};
  //std::map<SimEntity*, float> conc;
  ConcentrationGrid conc;
  int runID = 0;
//  int patchID = 0;
  int step;
};


class RACSnapshot
{
public:
	  public:
  //RACSnapshot(float r, juce::Array<float> f, juce::Array<float> pp, juce::Array<float> pm, juce::Array<float> sp) : rac(r), flows(f), posSpecificities(pp), negSpecificities(pm), specificity(sp)
  RACSnapshot(float r, juce::Array<float> f) : rac(r), flows(f)
    {}
  int runID = 0;
  int patchID = 0;
  int racID;
  int step;
  float rac;
  juce::Array<float> flows;
  //juce::Array<float> posSpecificities;
  //juce::Array<float> negSpecificities;
  //juce::Array<float> specificity;
};

class RACHist // RAC dynamics recorded in a single patch and for a single run
{
public:
	RACHist() {}
	RACHist(juce::Array<SimEntity*> e) { ents = e; }
	RACHist(juce::Array<SimEntity*> e, float s) { ents = e; pacScore = s; }
	juce::OwnedArray<RACSnapshot> hist;
	juce::Array<SimEntity*> ents;
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

  juce::Array<ConcentrationSnapshot> concentHistory; // concentration history
  //juce::Array<ConcentrationGrid> concentHistory; // concentration history
  juce::Array<RACSnapshot> racHistory; // RAC history
  std::map<PAC*, bool> wasRAC; // true if the PAC is on at some point "on" in the simulation (for drawing)
  
  
  ConcentrationSnapshot getLastConcentrationSnapshot()
  {
    return concentHistory.getUnchecked(concentHistory.size()-1);
  }
  
  ConcentrationSnapshot getConcentrationSnapshotForRunAndStep(int _run, int _step, int indexToStart)
  {
    int kbackward = indexToStart;
    int ntries = 0;
    ConcentrationSnapshot output;
    bool success = false;
    for (int kforward=indexToStart; kforward<concentHistory.size(); kforward++)
    {
      ntries++;
      kbackward--;
      if (concentHistory.getUnchecked(kforward).runID == _run && concentHistory.getUnchecked(kforward).step == _step)
      {
        output = concentHistory.getUnchecked(kforward);
        success = true;
        break;
      }
      if (kbackward>=0)
      {
        if (concentHistory.getUnchecked(kbackward).runID == _run && concentHistory.getUnchecked(kbackward).step == _step)
        {
          output = concentHistory.getUnchecked(kbackward);
          success = true;
          break;
        }
      }
    }
    // if this point is reached without success, return dummy snapshot with unexpected value, to control later for the success of the function
    jassert(success); // raise a message to tell user this function failed
    if (!success)
    {
      LOGWARNING("DynamicsHistory::getConcentrationSnapshotForRunAndStep() probably failed.");
      ConcentrationSnapshot dummy; // returning dummy snapshot. Should find a better outing
      dummy.step = -1;
      return dummy;
    }
    return output;
  }
  

  /*
  juce::Array<ConcentrationSnapshot> getConcentrationDynamicsForStep(int _stepid)
  {
    juce::Array<ConcentrationSnapshot> output;
    for (auto & cs : concentHistory)
    {
      for (auto & [patchent, c] : cs->conc)
      {
        if (patchent.first
      }
      if (cs.runID == _stepid)
        output.add(cs);
    }
    return output;
  }
  */
  
  juce::Array<ConcentrationSnapshot> getConcentrationDynamicsForRun(int _runid)
  {
    juce::Array<ConcentrationSnapshot> output;
    for (auto & cs : concentHistory)
    {
      if (cs.runID == _runid)
        output.add(cs);
    }
    return output;
  }
  /*
  Array<ConcentrationSnapshot> getConcentrationDynamicsForPatch(int _pid)
  {
    Array<ConcentrationSnapshot> output;
    for (auto & cs : concentHistory)
    {
      for (auto & [patchent, c] : cs->conc)
      {
        if (patchent.first == _pid)
        {
          ConcentrationSnapshot
          output.
        }
      }
      if (cs.patchID == _pid)
        output.add(cs);
    }
    return output;
  }
  */
  /*
  Array<ConcentrationSnapshot> getConcentrationDynamicsForRunAndPatch(int _runid, int _pid)
  {
    Array<ConcentrationSnapshot> output;
    for (auto & cs : concentHistory)
    {
      //if (cs.runID == _runid && cs.patchID == _pid)
      if (cs.runID == _runid && cs.patchID == _pid)
        output.add(cs);
    }
    return output;
  }
  */
  
  
  
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
  
  juce::Array<RACSnapshot> getRACDynamicsForRun(int _runid)
  {
    juce::Array<RACSnapshot> output;
    for (auto & rs : racHistory)
    {
      if (rs.runID == _runid)
        output.add(rs);
    }
    return output;
  }
  
  juce::Array<RACSnapshot> getRACDynamicsForPatch(int _pid)
  {
    juce::Array<RACSnapshot> output;
    for (auto & rs : racHistory)
    {
      if (rs.patchID == _pid)
        output.add(rs);
    }
    return output;
  }
  
  juce::Array<RACSnapshot> getRACDynamicsForPatchAndStep(int _pid, int _step, int startindex)
  {
    juce::Array<RACSnapshot> output;
    //for (auto & rs : racHistory)
    for (int k = startindex; k<racHistory.size(); k++)
    {
      RACSnapshot rs = racHistory.getUnchecked(k);
      if (rs.patchID == _pid && rs.step == _step)
        output.add(rs);
    }
    return output;
  }
  
  juce::Array<RACSnapshot> getRACDynamicsForRunAndPatch(int _runid, int _pid)
  {
    juce::Array<RACSnapshot> output;
    for (auto & rs : racHistory)
    {
      if (rs.runID == _runid && rs.patchID == _pid)
        output.add(rs);
    }
    return output;
  }
  
  

};
