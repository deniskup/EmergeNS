#pragma once
#include "JuceHeader.h"
#include <Eigen/Dense>
using namespace std;
using namespace juce;

int randInt(int i, int j);

float randFloat();

float randFloat(float a, float b);

float randFloat(float a);

void printMatrixToLog(const Eigen::MatrixXf& m);