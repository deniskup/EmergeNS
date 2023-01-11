
#include "GenerationUI.h"

GenerationUI::GenerationUI() : ShapeShifterContentComponent(Generation::getInstance()->niceName),
                               gener(Generation::getInstance())
{

    //TODO: add default UI like for BaseITems
}

GenerationUI::~GenerationUI()
{

}



void GenerationUI::resized()
{
    
}


