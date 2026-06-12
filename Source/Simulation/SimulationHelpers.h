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


// represents the concentration entities over the space grid at a given time
class ConcentrationSnapshot // concentration snapshot recorded for a single run.
{
public:
  ConcentrationSnapshot() {};
  //std::map<SimEntity*, float> conc;
  ConcentrationGrid conc;
  int runID = 0; // obsolete
  int step;
};

// represents the RAC activities over the spacegrid at a given time
class RACSnapshot
{
public:
	  public:
  RACSnapshot(juce::Array<float> r, juce::Array<juce::Array<float>> f) : rac(r), flows(f)
    {}
  int runID = 0; // obsolete
  int patchID = 0; // obsolete
  int racID;
  int step;
  juce::Array<float> rac; // rac values over the space grid
  juce::Array<juce::Array<float>> flows; // first dimension = space grid, second dimension = rac entity flows
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

  juce::Array<juce::Array<ConcentrationSnapshot>> concentHistory; // 1st dimension = runID | second dimension = time
  juce::Array<juce::Array<std::unordered_map<int, RACSnapshot>>> racHistory; // 1st dimension = runID | second dimension = time. map<pacID, RACSnapShot>
  std::map<PAC*, bool> wasRAC; // true if the PAC is on at some point "on" in the simulation (for drawing)

};
