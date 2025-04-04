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

class SimEntity;
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


class RACSnapshot
{
public:
	  public:
  RACSnapshot(float r, Array<float> f, Array<float> pp, Array<float> pm, Array<float> sp) : rac(r), flows(f), posSpecificities(pp), negSpecificities(pm), specificity(sp)
    {}
  float rac;
  Array<float> flows;
  Array<float> posSpecificities;
  Array<float> negSpecificities;
  Array<float> specificity;
};

class RACHist
{
public:
	RACHist() {}
	RACHist(Array<SimEntity*> e) { ents = e; }
	RACHist(Array<SimEntity*> e, float s) { ents = e; pacScore = s; }
	OwnedArray<RACSnapshot> hist;
	Array<SimEntity*> ents;
	float pacScore = 0.;
  bool wasRAC = false;
};


class SimRun
{
  SimRun(){};

  Array<Array<float>> concentHistory;
};
