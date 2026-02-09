#include "KineticLaw.h"



KineticLaw::KineticLaw(bool _useStochasticity, float _noiseEpsilon)
{
  useStochasticity = _useStochasticity;
  noiseEpsilon = _noiseEpsilon;
  if (useStochasticity)
    rgg = new RandomGausGenerator(0., 1.); // init random generator
}

KineticLaw::~KineticLaw()
{
  
}




void KineticLaw::SteppingReactionRates(OwnedArray<SimReaction>& _reactions, float dt, int patchid, bool updateReacFlows)
{
    
  // loop through reactions
  for (auto &reac : _reactions)
  {
    
    // for a sanity check
    //cout << "##### " << reac->name << " :" << endl;
    //cout << "\tassoc/dissoc k : " << reac->assocRate << " ; " << reac->dissocRate << endl;
    if (!reac->enabled)
      continue;
    
    // multiply reactants/products concentration together
    float minReacConcent = 100.;
    float mindReacConcent = 100.;
    float minProdConcent = 100.;
    float mindProdConcent = 100.;
    float reacConcent = 1.;
    float deterministicReacConcent = 1.;
    bool firstEnt = true;
    for (auto &ent : reac->reactants)
    {
      reacConcent *= ent->concent[patchid];
      deterministicReacConcent *= ent->deterministicConcent[patchid];
      //cout << "localReac::" << ent->name << ": " << ent->concent << "  :  " << ent->deterministicConcent << endl;
      if (ent == reac->reactants[0] || ent->concent[patchid] < minReacConcent)
        minReacConcent = ent->concent[patchid];
      if (ent == reac->reactants[0] || ent->deterministicConcent[patchid] < mindReacConcent)
        mindReacConcent = ent->deterministicConcent[patchid];
    }
    float prodConcent = 1.;
    float deterministicProdConcent = 1.;
    firstEnt = true;
    for (auto &ent : reac->products)
    {
      prodConcent *= ent->concent[patchid];
      deterministicProdConcent *= ent->deterministicConcent[patchid];
      if (ent == reac->products[0] || ent->concent[patchid] < minProdConcent)
        minProdConcent = ent->concent[patchid];
      if (ent == reac->products[0] || ent->deterministicConcent[patchid] < mindProdConcent)
        mindProdConcent = ent->deterministicConcent[patchid];
    }


    // multiply concentrations by froward/backward constant rates
    float directCoef = reacConcent * reac->assocRate;
    float deterministicDirectCoef = deterministicReacConcent * reac->assocRate;
    float reverseCoef = prodConcent * reac->dissocRate;
    float deterministicReverseCoef = deterministicProdConcent * reac->dissocRate;
    if (!reac->isReversible)
    {
      reverseCoef = 0.;
      deterministicReverseCoef = 0.;
    }
    
    // init increments
    float directIncr = directCoef * dt;
    float deterministicDirectIncr = deterministicDirectCoef * dt;
    float reverseIncr = reverseCoef * dt;
    float deterministicReverseIncr = deterministicReverseCoef * dt;

    //if (print)
    //{
     // cout << "K+ = " << reac->assocRate << endl;
     // for (auto & ent : reac->reactants)
     // {
     //   cout << "[" << ent->name << "] = " << ent->concent << endl;
     // }
      //cout << "forward incr = " << directIncr << " det. forward incr = " << deterministicDirectIncr  << endl;
    //}

    // adjust the increments depending on available entities
    directIncr = jmin(directIncr, minReacConcent);
    deterministicDirectIncr = jmin(deterministicDirectIncr, mindReacConcent);
    reverseIncr = jmin(reverseIncr, minProdConcent);
    deterministicReverseIncr = jmin(deterministicReverseIncr, mindProdConcent);

    // to treat reactions equally: save increments for later. increase() and decrease() store changes to make, and refresh() will effectively make them

    // increase and decrease entities
    for (auto &ent : reac->reactants)
    {
      ent->increase(patchid, reverseIncr);
      ent->deterministicIncrease(patchid, deterministicReverseIncr);
      ent->decrease(patchid, directIncr);
      ent->deterministicDecrease(patchid, deterministicDirectIncr);
    }
    for (auto &ent : reac->products)
    {
      ent->increase(patchid, directIncr);
      ent->deterministicIncrease(patchid, deterministicDirectIncr);
      ent->decrease(patchid, reverseIncr);
      ent->deterministicDecrease(patchid, deterministicReverseIncr);
    }
    
    
    // demographic noise
    if (useStochasticity)
    {
      float stoc_directIncr = sqrt(reac->assocRate) * noiseEpsilon;
      float stoc_reverseIncr = sqrt(reac->dissocRate) * noiseEpsilon;
      // for a sanity check
      //string testname = "2+2=4";
      //bool print(testname==reac->name ? true : false);
      
      // forward reaction
      map<SimEntity*, double> m;
      for (auto& ent : reac->reactants)
      {
        if (!m.count(ent)) // if entity has not been parsed already
        {
          stoc_directIncr *= sqrt(ent->concent[patchid]);
          m[ent] = 1;
        }
        else
        {
          float corrC = ent->concent[patchid] - noiseEpsilon * noiseEpsilon * m[ent];
          if (corrC > 0.) stoc_directIncr *= sqrt(corrC);
          else stoc_directIncr = 0.;
          m[ent]++;
        }
      }
      
      // random fluctuation of forward reaction associated to current timestep
      float sqrtdt = sqrt(dt);
      float directWiener = rgg->randomNumber()*sqrtdt; // gaus random in N(0, 1) x sqrt(dt)
      //if (print) cout << "forward wiener : " << directWiener << endl;
      stoc_directIncr *= directWiener;
      
      
      // backward reaction
      if (!reac->isReversible)
        stoc_reverseIncr = 0.;
      else
      {
        map<SimEntity*, double> mm;
        for (auto& ent : reac->products)
        {
          if (!mm.count(ent)) // if entity has not been parsed already
          {
            stoc_reverseIncr *= sqrt(ent->concent[patchid]);
            mm[ent] = 1;
          }
          else
          {
            float corrC = ent->concent[patchid] - noiseEpsilon * noiseEpsilon * mm[ent];
            if (corrC > 0.) stoc_reverseIncr *= sqrt(corrC);
            else stoc_reverseIncr = 0.;
            mm[ent]++;
          }
        }
      }
      
      // random fluctuation of forward reactions associated to current timestep
      float reverseWiener = rgg->randomNumber()*sqrtdt;
      //if (print) cout << "backward wiener : " << reverseWiener << endl;
      stoc_reverseIncr *= reverseWiener;
      
      // increase and decrease entities
      for (auto &ent : reac->reactants)
      {
        ent->increase(patchid, stoc_reverseIncr);
        ent->decrease(patchid, stoc_directIncr);
      }
      for (auto &ent : reac->products)
      {
        ent->increase(patchid, stoc_directIncr);
        ent->decrease(patchid, stoc_reverseIncr);
      }

      
    } // end if stochasticity

          
    // update flow needed only at checkpoints
    //if (isCheck || isMultipleRun)
    if (updateReacFlows)
    {
      //reac->flow = directCoef - reverseCoef;
      //reac->deterministicFlow = deterministicDirectCoef - deterministicReverseCoef;
      reac->flow.set(patchid, directCoef - reverseCoef);
      reac->deterministicFlow.set(patchid, deterministicDirectCoef - deterministicReverseCoef);
    }
  } // end reaction loop
  
  
}


void KineticLaw::SteppingInflowOutflowRates(OwnedArray<SimEntity>& _entities, int patchid, float dt)
{
  
  // loop over entities
  for (auto &ent : _entities)
  {
    ent->previousConcent.set(patchid, ent->concent[patchid]); // save concent in previousConcent to compute var speed
    
    // creation
    if (ent->primary)
    {
      float incr = ent->creationRate * dt;
      float deterministicIncr = ent->creationRate * dt;
      
      // demographic noise
      if (useStochasticity)
      {
        float stocIncr = sqrt(ent->creationRate) * noiseEpsilon;
        float wiener = rgg->randomNumber() * sqrt(dt);
        stocIncr *= wiener;
        incr -= stocIncr;
      } // end if stochasticity
      
      ent->increase(patchid, incr);
      ent->deterministicIncrease(patchid, deterministicIncr);
    }
    
    //destruction
    float rate = ent->concent[patchid] * ent->destructionRate;
    float incr = rate * dt;
    float deterministicRate = ent->deterministicConcent[patchid] * ent->destructionRate;
    float deterministicIncr = deterministicRate * dt;


    // demographic noise
    if (useStochasticity)
    {
      double stocIncr = sqrt(rate) * noiseEpsilon;
      float wiener = rgg->randomNumber() * sqrt(dt);
      stocIncr *= wiener;
      incr -= stocIncr;
    } // end if stochasticity
    
    ent->decrease(patchid, incr);
    ent->deterministicDecrease(patchid, deterministicIncr);
    

  } // end loop over entities

  

  
}


void KineticLaw::SteppingDiffusionRates(Patch& patch)
{
  
  // loop over neighbour patches of current patch
  for (auto& neighbour : patch.neighbours)
  {
    // loop over entities
    for (auto& ent : entities)
    {
      float grad = ent->concent[patch.id] - ent->concent[neighbour];
      float detgrad = ent->deterministicConcent[patch.id] - ent->deterministicConcent[neighbour];
      
      float incr = -grad * Space::getInstance()->diffConstant->floatValue();
      float detIncr = -detgrad * Space::getInstance()->diffConstant->floatValue();
      // atually it is -grad * kd / L where L is the distance between two patches. Included in kd definition
      
      if (stochasticity->boolValue())
      {
        // *** TODO
      }
      
      // increase concentrations of entities
      ent->increase(patch.id, incr);
      ent->deterministicIncrease(patch.id, incr);
    }
  }
}
