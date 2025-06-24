#include "Util.h"

// maybe rand functions to move to a file Util.c later
int randInt(int i, int j)
{
    if (j < i)
    {
        cerr << "Range [" << i << "," << j << "] incorrect, setting to " << i << endl;
        return i;
    }
    if (i == j)
        return i;
    return Random::getSystemRandom().nextInt(Range(i, j + 1));
}

float randFloat()
{
    return Random::getSystemRandom().nextFloat();
}

float randFloat(float a, float b)
{
    if (b < a)
    {
        cerr << "Range [" << a << "," << b << "] incorrect, setting to " << a << endl;
        return a;
    }
    if (a == b)
        return a;
    float r = randFloat();
    return (r * a + (1 - r) * b);
}

float randFloat(float a)
{
    return randFloat(0.f, a);
}