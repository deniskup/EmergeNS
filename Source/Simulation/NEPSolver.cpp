//  NEPSolver.cpp
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//

#include "NEPSolver.h"






 


//////////////////////////////////////////////////////////////////////////////////////////////////


NEPSolver::NEPSolver()
{
}

NEPSolver::~NEPSolver()
{
  //simul->removeAsyncSimulationListener(this);
  //simul->removeAsyncContainerListener(this);
}


double NEPSolver::evalHamiltonian(const StateVec q, const StateVec pu, bool useChangeOfVariable)
{
  //cout << "--- hamiltonian calculation --- " << endl;
  double H = 0.;
    
  jassert(pu.size() == q.size());
  if (pu.size() != q.size())
  {
    cout << "pu, q sizes : " << pu.size() << " " << q.size() << endl; 
    return H;
  }
  
  juce::Array<double> vecH;
  for (auto & reaction : crn.reactions)
  {
    if (!reaction->enabled)
      continue;
    //cout << reaction->name << endl;
    // forward reaction


    if (useChangeOfVariable)
    {
      double qfac_forward = 1.;
      double ufac_forward = 1.;
      double qfac_backward = 1.;
      double ufac_backward = 1.;
      for (auto & ent : reaction->reactants)
      {
        // forward reaction
        qfac_forward *= q.getUnchecked(ent->idSAT);
        jassert(pu.getUnchecked(ent->idSAT) > 0.);
        ufac_forward /= pu.getUnchecked(ent->idSAT);
        // backward reaction
        ufac_backward *= pu.getUnchecked(ent->idSAT);
      }
      for (auto & ent : reaction->products)
      {
        // forward reaction
        ufac_forward *= pu.getUnchecked(ent->idSAT);
        // backward reaction
        qfac_backward *= q.getUnchecked(ent->idSAT);
        jassert(pu.getUnchecked(ent->idSAT) > 0.);
        ufac_backward /= pu.getUnchecked(ent->idSAT);
      }
      H += (ufac_forward - 1.) * qfac_forward * reaction->assocRate;
      H += (ufac_backward - 1.) * qfac_backward * reaction->dissocRate;

    }
    else
    {
      double forward = reaction->assocRate;
      double sp1 = 0.;
      double pow1 = 1.;
      for (auto & ent : reaction->reactants)
      {
        sp1 -= pu.getUnchecked(ent->idSAT);
        pow1 *= q.getUnchecked(ent->idSAT);
      }
      for (auto & ent : reaction->products)
        sp1 += pu.getUnchecked(ent->idSAT);
      forward *= (exp(sp1) -1.) * pow1;
      H += forward;
    
    //cout << "spforward = " << sp1 << endl;
    //cout << "q^nu forward = " << pow1 << endl;
    //cout << "Hforward = " << forward << endl;
      
      // backward contribution
      double backward = reaction->dissocRate;
      double sp2 = 0.;
      double pow2 = 1.;
      for (auto & ent : reaction->reactants)
        sp2 += pu.getUnchecked(ent->idSAT);
      for (auto & ent : reaction->products)
      {
        sp2 -= pu.getUnchecked(ent->idSAT);
        pow2 *= q.getUnchecked(ent->idSAT);
      }
      backward *= (exp(sp2) - 1.) * pow2;
      H += backward;

    vecH.add(H);
    }
    
    
    //cout << "spbackward = " << sp2 << endl;
    //cout << "q^nu backward = " << pow2 << endl;
    //cout << "Hbackward = " << backward << endl;
    
    //cout << "current H = " << H << endl;
    
  } // end loop over reactions
  
  // loop over creation/destruction reactions,
  // formally treated as 0 <--> entity
  for (auto & ent : crn.entities)
  {
    if (useChangeOfVariable)
    {
      double creat = ent->creationRate * ( pu.getUnchecked(ent->idSAT) - 1. );
      H += creat;
    
      jassert(pu.getUnchecked(ent->idSAT) > 0.);
      double dest = ent->destructionRate * ( 1./pu.getUnchecked(ent->idSAT) - 1. ) * q.getUnchecked(ent->idSAT);
      H += dest;
    }
    else
    {
      double creat = ent->creationRate * ( exp(pu.getUnchecked(ent->idSAT)) - 1. );
      H += creat;
    
      double dest = ent->destructionRate * ( exp(-1.*pu.getUnchecked(ent->idSAT)) - 1. ) * q.getUnchecked(ent->idSAT);
      H += dest;
    }
  }
  
  
  /*
  cout << "--- hamiltonian check --- " << endl;
  for (int k=0; k<vecH.size(); k++)
  {
    cout << "H" << k << " = " << vecH.getUnchecked(k) << endl;
  }
  cout << "Htot = " << H << endl;
  */
  
  return crn.timescale_factor * H;
}




StateVec NEPSolver::evalHamiltonianGradientWithP(const StateVec q, const StateVec p)
{/*
  cout << "--- evalHamiltonianGradientWithP() ---" << endl;
  cout << setprecision(8) << endl;
  cout << "q = ";
  for (auto & f : q)
    cout << f << " ";
  cout << endl;
  cout << "p = ";
  for (auto & f : p)
    cout << f << " ";
  cout << endl;
  */
  // init output and intermediate vectors
  int dim = crn.entities.size();
  StateVec gradpH;
  gradpH.insertMultiple(0, 0., dim);
  
  jassert(p.size() == dim && q.size() == dim);
  if (p.size() != q.size())
    return gradpH;
  /*
  cout << "dH/dp init = ";
  for (auto & f : gradpH)
    cout << f << " ";
  cout << endl;
  */
  // loop over reactions
  for (auto & reaction : crn.reactions)
  {
    if (!reaction->enabled)
      continue;
    //cout << endl << reaction->name << endl;
    // forward reaction
    double forward = reaction->assocRate;
    double sp1 = 0.;
    double pow1 = 1.;
    StateVec prevec1;
    prevec1.insertMultiple(0, 0., q.size());
    for (auto & ent : reaction->reactants)
    {
      sp1 -= p.getUnchecked(ent->idSAT);
      pow1 *= q.getUnchecked(ent->idSAT);
      prevec1.setUnchecked(ent->idSAT, prevec1.getUnchecked(ent->idSAT) - 1.);
    }
    for (auto & ent : reaction->products)
    {
      sp1 += p.getUnchecked(ent->idSAT);
      prevec1.setUnchecked(ent->idSAT, prevec1.getUnchecked(ent->idSAT) + 1.);
    }
    forward *= exp(sp1) * pow1;
    /*
    cout << "(ybeta - yalpha) forward = ";
    for (auto p : prevec1)
      cout << p << " ";
    cout << endl;
    cout << "s.p = " << sp1 << endl;
    cout << "exp(s.p) = " << exp(sp1) << endl;
    cout << "k = " << reaction->assocRate << endl;
    cout << "monom = " << pow1 << endl;
    cout << "forward term = " << forward << endl;
    */
    
    // backward contribution
    double backward = reaction->dissocRate;
    double sp2 = 0.;
    double pow2 = 1.;
    StateVec prevec2;
    prevec2.insertMultiple(0, 0., q.size());
    for (auto & ent : reaction->reactants)
    {
      sp2 += p.getUnchecked(ent->idSAT);
      prevec2.setUnchecked(ent->idSAT, prevec2.getUnchecked(ent->idSAT) + 1.);
    }
    for (auto & ent : reaction->products)
    {
      sp2 -= p.getUnchecked(ent->idSAT);
      pow2 *= q.getUnchecked(ent->idSAT);
      prevec2.setUnchecked(ent->idSAT, prevec2.getUnchecked(ent->idSAT) - 1.);
    }
    backward *= exp(sp2) * pow2;
    /*
    cout << "(ybeta - yalpha) backward = ";
    for (auto p : prevec2)
      cout << p << " ";
    cout << endl;
    cout << "s.p = " << sp2 << endl;
    cout << "exp(s.p) = " << exp(sp2) << endl;
    cout << "k = " << reaction->dissocRate << endl;
    cout << "monom = " << pow2 << endl;
    cout << "backward term = " << backward << endl;
    */
    // update output array with forward reaction
    juce::Array<double> thisgrad;
    for (int k=0; k<gradpH.size(); k++)
    {
      //cout <<  prevec1.getUnchecked(k)*forward + prevec2.getUnchecked(k)*backward << "   ";
      thisgrad.add(prevec1.getUnchecked(k)*forward + prevec2.getUnchecked(k)*backward);
      gradpH.setUnchecked(k, gradpH.getUnchecked(k) + prevec1.getUnchecked(k)*forward + prevec2.getUnchecked(k)*backward );
    }
/*
    cout << "grad to this reac : ";
    for (auto & ele : thisgrad)
      cout << ele << " ";
    cout << endl;
    cout << "current dH/dp : ";
    for (auto & ele : gradpH)
      cout << ele << " ";
    cout << endl;
*/
  } // end loop over reactions
  
  
  // creation / destruction reactions, formally treated as 0 <--> entity
  for (auto & ent : crn.entities)
  {
    //cout << "0 <--> " << ent->name << endl;
    double creatfact = ent->creationRate * exp(p.getUnchecked(ent->idSAT));
    gradpH.setUnchecked(ent->idSAT, gradpH.getUnchecked(ent->idSAT) + creatfact);
    //cout << "grapH coord " << ent->idSAT << " += " << creatfact << " for forward" << endl;
    
    double destfact = ent->destructionRate * exp(-1.*p.getUnchecked(ent->idSAT)) * q.getUnchecked(ent->idSAT);
    gradpH.setUnchecked(ent->idSAT, gradpH.getUnchecked(ent->idSAT) - destfact);
    //cout << "grapH coord " << ent->idSAT << " -= " << destfact << " for backward" << endl;
    /*
    cout << "current dH/dp : ";
    for (auto & ele : gradpH)
      cout << ele << " ";
    cout << endl;
    */
  }
  
  
  for (int m=0; m<gradpH.size(); m++)
    gradpH.setUnchecked(m, gradpH.getUnchecked(m)*crn.timescale_factor);
  
  return gradpH;
}



StateVec NEPSolver::evalUtimesHamiltonianGradientWithU(const StateVec q, const StateVec u)
{
  
  //cout << "--- evalHamiltonianGradientWithU() ---" << endl;

  /*
  cout << "q = ";
  for (auto & qm : q)
    cout << qm << " ";
  cout << endl;
  cout << "u = ";
  for (auto & um : u)
    cout << um << " ";
  cout << endl;
  */
  
  // output gradient vector
  int dim = crn.entities.size();
  StateVec graduH;
  graduH.insertMultiple(0, 0., dim);
  
  jassert(u.size() == dim && q.size() == dim);
  if (u.size() != q.size())
    return graduH;
  

  // loop over reactions
  for (auto & reaction : crn.reactions)
  {
    if (!reaction->enabled)
      continue;
    //cout << reaction->name << endl;

    double forward = reaction->assocRate;
    double backward = reaction->dissocRate;
    juce::Array<int> forward_prevec;
    juce::Array<int> backward_prevec;
    forward_prevec.insertMultiple(0, 0, dim);
    backward_prevec.insertMultiple(0, 0, dim);
    // loop over reaction reactants
    for (auto & reactant: reaction->reactants)
    {
      // forward reaction
      forward *= q.getUnchecked(reactant->idSAT);
      jassert(u.getUnchecked(reactant->idSAT) > 0.);
      forward /= u.getUnchecked(reactant->idSAT);
      forward_prevec.setUnchecked(reactant->idSAT, forward_prevec.getUnchecked(reactant->idSAT) - 1);
      // backwward reaction
      backward *= u.getUnchecked(reactant->idSAT);
      backward_prevec.setUnchecked(reactant->idSAT, backward_prevec.getUnchecked(reactant->idSAT) + 1);
    }
    for (auto & reactant: reaction->products)
    {
      // foward reaction
      forward *= u.getUnchecked(reactant->idSAT);
      forward_prevec.setUnchecked(reactant->idSAT, forward_prevec.getUnchecked(reactant->idSAT) + 1);
      // backward reaction
      backward *= q.getUnchecked(reactant->idSAT);
      jassert(u.getUnchecked(reactant->idSAT) > 0.);
      backward /= u.getUnchecked(reactant->idSAT);
      backward_prevec.setUnchecked(reactant->idSAT, backward_prevec.getUnchecked(reactant->idSAT) - 1);
    }
    

    for (int k=0; k<graduH.size(); k++)
    {
      // forward reaction contribution
      int yk_forward = forward_prevec.getUnchecked(k);
      if (yk_forward != 0)
      {
        double comp = (double) yk_forward * forward;
        graduH.setUnchecked(k, graduH.getUnchecked(k) + comp);
        //graduH.setUnchecked(k, graduH.getUnchecked(k) + prevec1.getUnchecked(k)*forward + prevec2.getUnchecked(k)*backward );
      }
      // backward reaction contribution
      int yk_backward = backward_prevec.getUnchecked(k);
      if (yk_backward != 0)
      {
        double comp = (double) yk_backward * backward;
        graduH.setUnchecked(k, graduH.getUnchecked(k) + comp);
        //graduH.setUnchecked(k, graduH.getUnchecked(k) + prevec1.getUnchecked(k)*forward + prevec2.getUnchecked(k)*backward );
      }
    }
    
  } // end reaction loop
  
  
  // creation / destruction reactions, formally treated as 0 <--> entity
  for (auto & ent : crn.entities)
  {
    //cout << "0 <--> " << ent->name << endl;
    if (ent->creationRate > 0.)
    {
      double forward = ent->creationRate * u.getUnchecked(ent->idSAT);
      graduH.setUnchecked(ent->idSAT, graduH.getUnchecked(ent->idSAT) + forward);
    }

    // destruction flow prop to qent and 1/uent
    jassert(u.getUnchecked(ent->idSAT) > 0.);
    double backward = ent->destructionRate * q.getUnchecked(ent->idSAT) / u.getUnchecked(ent->idSAT);
    graduH.setUnchecked(ent->idSAT, graduH.getUnchecked(ent->idSAT) - backward);
    //cout << "kd = " << ent->destructionRate << endl;
    //cout << "exp factor = " << exp(-1.*p.getUnchecked(ent->idSAT)) - 1. << endl;
    //cout << "grad coord " << ent->idSAT << " -= " << destfact << endl;
    /*
    cout << "dH/dq current = ";
    for (auto & g : gradqH)
      cout << g << " ";
    cout << endl;
     */
  }
  
  /*
  cout << "total gradient = " ;
  for (auto & g : gradqH)
    cout << g << " " ;
  cout << endl << endl;
  */
  
  for (int m=0; m<graduH.size(); m++)
    graduH.setUnchecked(m, graduH.getUnchecked(m) * crn.timescale_factor);

  return graduH;
  
}




StateVec NEPSolver::evalHamiltonianGradientWithU(const StateVec q, const StateVec u)
{
  
  //cout << "--- evalHamiltonianGradientWithU() ---" << endl;

  /*
  cout << "q = ";
  for (auto & qm : q)
    cout << qm << " ";
  cout << endl;
  cout << "u = ";
  for (auto & um : u)
    cout << um << " ";
  cout << endl;
  */
  
  // output gradient vector
  //StateVec gradqH(q.size(), 0.);
  int dim = crn.entities.size();
  StateVec graduH;
  graduH.insertMultiple(0, 0., dim);
  
  jassert(u.size() == dim && q.size() == dim);
  if (u.size() != q.size())
    return graduH;
  
  /*
  cout << "dH/dq init = ";
  for (auto & g : gradqH)
    cout << g << " ";
  cout << endl;
  */
  // loop over reactions
  for (auto & reaction : crn.reactions)
  {
    if (!reaction->enabled)
      continue;
    //cout << reaction->name << endl;
    
    // stoichiometric vector
    std::map<int, int> ytotal; // <int, int> --> <idSAT, power>
    for (auto & reactant: reaction->reactants)
    {
      ytotal[reactant->idSAT]--;
    }
    for (auto & product: reaction->products)
    {
      ytotal[product->idSAT]++;
    }
    /*
    cout << "-- stoec vectors --" << endl;
    cout << "yreactants = ";
    for (auto & y : yreactants)
      cout << y << " ";
    cout << endl;
    cout << "yproducts = ";
    for (auto & y : yproducts)
      cout << y << " ";
    cout << endl;
    cout << "forward MAK polynom : ";
    for (auto & [key, val] : makforward)
      cout << " q_" << key << "^" << val;
    cout << endl;
    cout << "backward MAK polynom : ";
    for (auto & [key, val] : makbackward)
      cout << " q_" << key << "^" << val;
    cout << endl;
    */
    
    // forward prefactor
    //cout << "-- forward reaction grad calc. --" << endl;
    double forward_prefactor = reaction->assocRate;
    // multiply by kin mass action
    for (auto & reactant : reaction->reactants)
      forward_prefactor *= q.getUnchecked(reactant->idSAT);

    // backward prefactor
    double backward_prefactor = reaction->dissocRate;
    // multiply by kin mass action
    for (auto & product : reaction->products)
      backward_prefactor *= q.getUnchecked(product->idSAT);


    for (auto & [id, exponent] : ytotal) 
    {
      //cout << "monom = " << exponent << "*" << q.getUnchecked(id) << "^" << exponent-1;
      double monom_forward = exponent * pow(u.getUnchecked(id), exponent-1.); // derivative of q_id
      double monom_backward = (-1. * exponent) * pow(u.getUnchecked(id), (-1.*exponent)-1.); // derivative of q_id
      for (auto & [id2, exponent2] : ytotal) // multiply by other u_j different from u_id
      {
        if (id2==id)
          continue;
        //cout << " * " << q.getUnchecked(id2) << "^" << exponent2 << " * ";
        monom_forward *= pow(u.getUnchecked(id2), exponent2);
        monom_backward *= pow(u.getUnchecked(id2), -1*exponent2);
      }
      //cout << endl;
      //cout << "gradH_" << id << " += " << forward_prefactor*monom << endl;
      graduH.setUnchecked(id, graduH.getUnchecked(id) + forward_prefactor*monom_forward + backward_prefactor*monom_backward);
/*
      cout << "dH/dq current = ";
      for (auto & g : gradqH)
        cout << g << " ";
      cout << endl;
      */
    }
  } // end reaction loop
  
  
  // creation / destruction reactions, formally treated as 0 <--> entity
  for (auto & ent : crn.entities)
  {
    //cout << "0 <--> " << ent->name << endl;
    // creation 
    if (ent->creationRate > 0.)
    {
      double creatfact = ent->creationRate;
      graduH.setUnchecked(ent->idSAT, graduH.getUnchecked(ent->idSAT) + creatfact);
    }
    
    // destruction flow prop to qent
    //cout << "backward" << endl;
    jassert(u.getUnchecked(ent->idSAT) > 0.);
    double destfact = ent->destructionRate *-1. / (u.getUnchecked(ent->idSAT)*u.getUnchecked(ent->idSAT)) * q.getUnchecked(ent->idSAT);
    graduH.setUnchecked(ent->idSAT, graduH.getUnchecked(ent->idSAT) - destfact);
    //cout << "kd = " << ent->destructionRate << endl;
    //cout << "exp factor = " << exp(-1.*p.getUnchecked(ent->idSAT)) - 1. << endl;
    //cout << "grad coord " << ent->idSAT << " -= " << destfact << endl;
    /*
    cout << "dH/dq current = ";
    for (auto & g : gradqH)
      cout << g << " ";
    cout << endl;
     */
  }
  
  /*
  cout << "total gradient = " ;
  for (auto & g : gradqH)
    cout << g << " " ;
  cout << endl << endl;
  */
  
  for (int m=0; m<graduH.size(); m++)
    graduH.setUnchecked(m, graduH.getUnchecked(m) * crn.timescale_factor);

  return graduH;
  
}






juce::dsp::Matrix<double> NEPSolver::evalHamiltonianHessianWithU(const StateVec q, const StateVec u)
{
  
  //cout << "--- evalHamiltonianHessianWithU() ---" << endl;

  /*
  cout << "q = ";
  for (auto & qm : q)
    cout << qm << " ";
  cout << endl;
  cout << "u = ";
  for (auto & um : u)
    cout << um << " ";
  cout << endl;
  */
  
   // init hessian as null matrix
  int dim = crn.entities.size();
  juce::dsp::Matrix<double> nullmatrix(dim, dim);
  nullmatrix.clear(); // Fills the contents of the matrix with zeroes.
  juce::dsp::Matrix<double> hess(nullmatrix);
  
  
  jassert(u.size() == q.size());
  if (u.size() != q.size())
    return nullmatrix;
  
  /*
  cout << "dH/dq init = ";
  for (auto & g : gradqH)
    cout << g << " ";
  cout << endl;
  */
  // loop over reactions
  for (auto & reaction : crn.reactions)
  {
    if (!reaction->enabled)
      continue;
    //cout << reaction->name << endl;
    
     // stoichiometric vector
    std::map<int, int> ytotal; // <int, int> --> <idSAT, power>
    for (auto & reactant: reaction->reactants)
    {
      ytotal[reactant->idSAT]--;
    }
    for (auto & product: reaction->products)
    {
      ytotal[product->idSAT]++;
    }
   

    for (auto & [i, powi] : ytotal) 
    {
      for (auto & [j, powj] : ytotal)
      {
        if (i==j)
        {
          // forward reaction
          if (powi != 1 || powi != 0) // contribution to hessian for forward reaction
          {
            double forward = reaction->assocRate * (double) powi * (double) (powi-1.) * pow(u.getUnchecked(i), powi-2.);
            for (auto& reactant : reaction->reactants)
              forward *= q.getUnchecked(reactant->idSAT);
            for (auto & [k, powk] : ytotal)
            {
              if (k==i)
                continue;
              forward *= pow(u.getUnchecked(k), powk);
            }
            hess(i, i) += forward;
          }
          // backward reaction
          if (powi != -1 || powi != 0) // contribution to hessian for backward reaction
          {
            double minuspowi = -1. * powi;
            double backward = reaction->dissocRate * minuspowi * (minuspowi-1.) * pow(u.getUnchecked(i), (int) minuspowi-2.);
            for (auto& product : reaction->products)
              backward *= q.getUnchecked(product->idSAT);
            for (auto & [k, powk] : ytotal)
            {
              if (k==i)
                continue;
              int negpowk = -1 * powk;
              backward *= pow(u.getUnchecked(k), negpowk);
            }
            hess(i, i) += backward;
          }
        }
        else // i != j
        {
          // forward reaction
          if (powi != 0 || powj != 0) // contribution to hessian for forward reaction
          {
            double forward = reaction->assocRate * (double) powi * (double) powj * pow(u.getUnchecked(i), powi-1) * pow(u.getUnchecked(j), powj-1);
            for (auto& reactant : reaction->reactants)
              forward *= q.getUnchecked(reactant->idSAT);
            for (auto & [k, powk] : ytotal)
            {
              if (k==i || k==j)
                continue;
              forward *= pow(u.getUnchecked(k), powk);
            }
            hess(i, j) += forward;
          }
          // backward reaction
          if (powi != 0 || powj != 0) // contribution to hessian for backward reaction
          {
            int negpowi = -1 * powi;
            int negpowj = -1 * powj;
            double backward = reaction->dissocRate * (double) negpowi * (double) negpowj * pow(u.getUnchecked(i), negpowi-1) * pow(u.getUnchecked(j), negpowj-1);
            for (auto& product : reaction->products)
              backward *= q.getUnchecked(product->idSAT);
            for (auto & [k, powk] : ytotal)
            {
              if (k==i || k==j)
                continue;
              int negpowk = -1 * powk;
              backward *= pow(u.getUnchecked(k), negpowk);
            }
            hess(i, j) += backward;
          }
        }
      } 
    }
  } // end reaction loop
  
  
  // creation / destruction reactions, formally treated as 0 <--> entity
  for (auto & ent : crn.entities)
  {
    //cout << "0 <--> " << ent->name << endl;
    // forward contribution is null since creation term is linear in ui
    
    // destruction term is in 1/ui, hence only contribution to hessian is prop to 2/ui^3
    //cout << "backward" << endl;
    jassert(u.getUnchecked(ent->idSAT) > 0.);
    double destfact = ent->destructionRate;
    destfact *= 2. / (u.getUnchecked(ent->idSAT)*u.getUnchecked(ent->idSAT*u.getUnchecked(ent->idSAT))); 
    destfact *= q.getUnchecked(ent->idSAT);
    hess(ent->idSAT, ent->idSAT) += destfact;
    //cout << "kd = " << ent->destructionRate << endl;
    //cout << "exp factor = " << exp(-1.*p.getUnchecked(ent->idSAT)) - 1. << endl;
    //cout << "grad coord " << ent->idSAT << " -= " << destfact << endl;
    /*
    cout << "dH/dq current = ";
    for (auto & g : gradqH)
      cout << g << " ";
    cout << endl;
     */
  }
  
  /*
  cout << "total gradient = " ;
  for (auto & g : gradqH)
    cout << g << " " ;
  cout << endl << endl;
  */
  
  // multiply by timescale factor
  for (int i=0; i<hess.getSize().getUnchecked(0); i++)
  {
    for (int j=0; j<hess.getSize().getUnchecked(0); j++)
    {
      hess(i, j) *= crn.timescale_factor;
    }
  }
  return hess;
  
}




juce::dsp::Matrix<double> NEPSolver::evalHamiltonianHessianWithP(const StateVec q, const StateVec p)
{
  /*
    cout << "--- evalHamiltonianHessianWithP() ---" << endl;
    cout << setprecision(8) << endl;
    cout << "q = ";
    for (auto & f : q)
      cout << f << " ";
    cout << endl;
    cout << "p = ";
    for (auto & f : p)
      cout << f << " ";
    cout << endl;
    */
  
  // init hessian as null matrix
  int dim = crn.entities.size();
  juce::dsp::Matrix<double> nullmatrix(dim, dim);
  nullmatrix.clear(); // Fills the contents of the matrix with zeroes.
  juce::dsp::Matrix hess(nullmatrix);
  
  
  jassert(p.size() == q.size());
  if (p.size() != q.size())
    return nullmatrix;
    
  
    // loop over reactions
    for (auto & reaction : crn.reactions)
    {
      if (!reaction->enabled)
        continue;
      
      //cout << reaction->name << endl;
      // forward reaction
      double forward = reaction->assocRate;
      double sp1 = 0.;
      double pow1 = 1.;
      StateVec prevec1;
      prevec1.insertMultiple(0, 0., q.size());
      for (auto & ent : reaction->reactants)
      {
        sp1 -= p.getUnchecked(ent->idSAT);
        pow1 *= q.getUnchecked(ent->idSAT);
        prevec1.setUnchecked(ent->idSAT, prevec1.getUnchecked(ent->idSAT) - 1.);
      }
      for (auto & ent : reaction->products)
      {
        sp1 += p.getUnchecked(ent->idSAT);
        prevec1.setUnchecked(ent->idSAT, prevec1.getUnchecked(ent->idSAT) + 1.);
      }
      forward *= exp(sp1) * pow1;
      

      /*
      cout << "(ybeta - yalpha) forward = ";
      for (auto p : prevec1)
        cout << p << " ";
      cout << endl;
      cout << "s.p = " << sp1 << endl;
      cout << "exp(s.p) = " << exp(sp1) << endl;
      cout << "k = " << reaction->assocRate << endl;
      cout << "monom = " << pow1 << endl;
      cout << "forward term = " << forward << endl;
      */
      
      // backward contribution
      double backward = reaction->dissocRate;
      double sp2 = 0.;
      double pow2 = 1.;
      StateVec prevec2;
      prevec2.insertMultiple(0, 0., q.size());
      for (auto & ent : reaction->reactants)
      {
        sp2 += p.getUnchecked(ent->idSAT);
        prevec2.setUnchecked(ent->idSAT, prevec2.getUnchecked(ent->idSAT) + 1.);
      }
      for (auto & ent : reaction->products)
      {
        sp2 -= p.getUnchecked(ent->idSAT);
        pow2 *= q.getUnchecked(ent->idSAT);
        prevec2.setUnchecked(ent->idSAT, prevec2.getUnchecked(ent->idSAT) - 1.);
      }
      backward *= exp(sp2) * pow2;
      
      
      /*
      cout << "(ybeta - yalpha) backward = ";
      for (auto p : prevec2)
        cout << p << " ";
      cout << endl;
      cout << "s.p = " << sp2 << endl;
      cout << "exp(s.p) = " << exp(sp2) << endl;
      cout << "k = " << reaction->dissocRate << endl;
      cout << "monom = " << pow2 << endl;
      cout << "backward term = " << backward << endl;
      */
      
      // add contributions to hessian matrix
      for (int i=0; i<hess.getSize().getUnchecked(0); i++)
      {
        for (int j=0; j<hess.getSize().getUnchecked(1); j++)
        {
          double el = prevec1.getUnchecked(i)*prevec1.getUnchecked(j)*forward + prevec2.getUnchecked(i)*prevec2.getUnchecked(j)*backward;
          //cout << "modyfing element (" << i << "," << j << ") by " << el << endl;
          hess(i, j) += el;
        }
      }
      
      
  /*
      cout << "d^2H/dp^2 to this reac : ";
      cout << endl;
  */
    } // end loop over reactions
    
    
    // creation / destruction reactions, formally treated as 0 <--> entity
    for (auto & ent : crn.entities)
    {
      // forward reaction = creation
      double creatfact = ent->creationRate * exp(p.getUnchecked(ent->idSAT));
      hess(ent->idSAT, ent->idSAT) += creatfact;
      //cout << "grapH coord " << ent->idSAT << " += " << creatfact << " for forward" << endl;
      
      // backward reaction = destruction
      double destfact = ent->destructionRate * exp(-1.*p.getUnchecked(ent->idSAT)) * q.getUnchecked(ent->idSAT);
      hess(ent->idSAT, ent->idSAT) += destfact;
      //cout << "grapH coord " << ent->idSAT << " -= " << destfact << " for backward" << endl;
      /*
      cout << "current dH/dp : ";
      for (auto & ele : gradpH)
        cout << ele << " ";
      cout << endl;
      */
    }
    
    // multiply by timescale factor
    for (int i=0; i<hess.getSize().getUnchecked(0); i++)
    {
      for (int j=0; j<hess.getSize().getUnchecked(0); j++)
      {
        hess(i, j) *= crn.timescale_factor;
      }
    }
    
    return hess;
  
}




StateVec NEPSolver::evalHamiltonianGradientWithQ(const StateVec q, const StateVec p)
{
  
  //cout << "--- evalHamiltonianGradientWithQ() ---" << endl;

  /*
  cout << "q = ";
  for (auto & qm : q)
    cout << qm << " ";
  cout << endl;
  cout << "p = ";
  for (auto & pm : p)
    cout << pm << " ";
  cout << endl;
  */
  
  // output gradient vector
  //StateVec gradqH(q.size(), 0.);
  int dim = crn.entities.size();
  StateVec gradqH;
  gradqH.insertMultiple(0, 0., dim);
  
  jassert(p.size() == dim && q.size() == dim);
  if (p.size() != q.size())
    return gradqH;
  
  /*
  cout << "dH/dq init = ";
  for (auto & g : gradqH)
    cout << g << " ";
  cout << endl;
  */
  // loop over reactions
  for (auto & reaction : crn.reactions)
  {
    if (!reaction->enabled)
      continue;
    //cout << reaction->name << endl;
    
    // set stoechiometric vector of reactants and product
    StateVec yreactants, yproducts;
    yreactants.insertMultiple(0, 0., q.size());
    yproducts.insertMultiple(0, 0., q.size());
    // keep track of MAK monom
    map<int, int> makforward; // <int, int> --> <idSAT, power>
    map<int, int> makbackward; //
    for (auto & r: reaction->reactants)
    {
      yreactants.setUnchecked(r->idSAT, yreactants.getUnchecked(r->idSAT) + 1 );
      makforward[r->idSAT]++;
    }
    for (auto & p: reaction->products)
    {
      yproducts.setUnchecked(p->idSAT, yproducts.getUnchecked(p->idSAT) + 1 );
      makbackward[p->idSAT]++;
    }
    /*
    cout << "-- stoec vectors --" << endl;
    cout << "yreactants = ";
    for (auto & y : yreactants)
      cout << y << " ";
    cout << endl;
    cout << "yproducts = ";
    for (auto & y : yproducts)
      cout << y << " ";
    cout << endl;
    cout << "forward MAK polynom : ";
    for (auto & [key, val] : makforward)
      cout << " q_" << key << "^" << val;
    cout << endl;
    cout << "backward MAK polynom : ";
    for (auto & [key, val] : makbackward)
      cout << " q_" << key << "^" << val;
    cout << endl;
    */
    
    // forward reaction
    //cout << "-- forward reaction grad calc. --" << endl;
    double forward_prefactor = reaction->assocRate;
    double spfor = 0.;
    for (int m=0; m<p.size(); m++)
    {
      //cout << "sp check:: " << (yproducts.getUnchecked(m)-yreactants.getUnchecked(m)) << " * " << p.getUnchecked(m) << endl;
      spfor += (yproducts.getUnchecked(m)-yreactants.getUnchecked(m)) * p.getUnchecked(m);
    }
    forward_prefactor *= (exp(spfor) - 1.);
    //cout << "forward s.p = " << spfor << endl;
    //cout << "k = " << reaction->assocRate << endl;
    //cout << "forward prefac = " << forward_prefactor << endl;
    // now derivative of polynom in concentration
    // loop over all entities involved in MAK
    for (auto & [id, exponent] : makforward)
    {
      //cout << "monom = " << exponent << "*" << q.getUnchecked(id) << "^" << exponent-1;
      double monom = exponent * pow(q.getUnchecked(id), exponent-1.); // derivative of q_id
      for (auto & [id2, exponent2] : makforward) // multiply by other q_j different from q_id
      {
        if (id2==id)
          continue;
        //cout << " * " << q.getUnchecked(id2) << "^" << exponent2 << " * ";
        monom *= pow(q.getUnchecked(id2), exponent2);
      }
      //cout << endl;
      //cout << "gradH_" << id << " += " << forward_prefactor*monom << endl;
      gradqH.setUnchecked(id, gradqH.getUnchecked(id) + forward_prefactor*monom);
/*
      cout << "dH/dq current = ";
      for (auto & g : gradqH)
        cout << g << " ";
      cout << endl;
      */
    }
    
  
    
    // backward reaction
    //cout << "-- backward grad calc. --" << endl;
    double backward_prefactor = reaction->dissocRate;
    double spback = 0.;
    for (int m=0; m<p.size(); m++)
      spback += (yreactants.getUnchecked(m)-yproducts.getUnchecked(m)) * p.getUnchecked(m);
    backward_prefactor *= (exp(spback) - 1.);
    //cout << "s.p = " << spback << endl;
    //cout << "k = " << reaction->dissocRate << endl;
    //cout << "backward prefac = " << backward_prefactor << endl;
    // now derivative of polynom in concentration
    for (auto & [id, exponent] : makbackward)
    {
      //cout << "monom = " << exponent << "*" << q.getUnchecked(id) << "^" << exponent-1;
      double monom = exponent * pow(q.getUnchecked(id), exponent-1.);
      for (auto & [id2, exponent2] : makbackward)
      {
        if (id2==id)
          continue;
        //cout << " * " << q.getUnchecked(id2) << "^" << exponent2 << " * ";
        monom *= pow(q.getUnchecked(id2), exponent2);
      }
      //cout << endl;
      //cout << "gradH_" << id << " += " << backward_prefactor*monom << endl;
      gradqH.setUnchecked(id, gradqH.getUnchecked(id) + backward_prefactor*monom);
      /*
      cout << "dH/dq current = ";
      for (auto & g : gradqH)
        cout << g << " ";
      cout << endl;
      */
    }
    
  } // end reaction loop
  
  
  // creation / destruction reactions, formally treated as 0 <--> entity
  for (auto & ent : crn.entities)
  {
    //cout << "0 <--> " << ent->name << endl;
    // creation flow does not depend on q, so gradient is null
    
    // destruction flow prop to qent
    //cout << "backward" << endl;
    double destfact = ent->destructionRate * ( exp(-1.*p.getUnchecked(ent->idSAT)) - 1.);
    gradqH.setUnchecked(ent->idSAT, gradqH.getUnchecked(ent->idSAT) + destfact);
    //cout << "kd = " << ent->destructionRate << endl;
    //cout << "exp factor = " << exp(-1.*p.getUnchecked(ent->idSAT)) - 1. << endl;
    //cout << "grad coord " << ent->idSAT << " -= " << destfact << endl;
    /*
    cout << "dH/dq current = ";
    for (auto & g : gradqH)
      cout << g << " ";
    cout << endl;
     */
  }
  
  /*
  cout << "total gradient = " ;
  for (auto & g : gradqH)
    cout << g << " " ;
  cout << endl << endl;
  */
  
  for (int m=0; m<gradqH.size(); m++)
    gradqH.setUnchecked(m, gradqH.getUnchecked(m) * crn.timescale_factor);

  return gradqH;
  
}






//double NEPSolver::calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t)
juce::Array<double> NEPSolver::calculateAction(const Curve& qc, const Curve& pc, const juce::Array<double>& t)
{
  //cout << "-- calculateAction() --" << endl;
  // check that pcurve, qcurve and tcurve have the same size
  jassert(qc.size() == pc.size());
  jassert(qc.size() == t.size());
  
  //cout << "--- calculate action ---" << endl;
  
  /*
  for (int point=0; point<nPoints; point++)
  {
    cout << "\npoint #" << point << endl;
    cout << "t = " << t.getUnchecked(point) << endl;
    cout << "q = ";
    for (auto & q : qc.getUnchecked(point))
      cout << q << " ";
    cout << endl;
    cout << "p = ";
    for (auto p  : pc.getUnchecked(point))
      cout << p << " ";
    cout << endl;
  }
  */
    
  juce::Array<double> hamilt;
  for (int i=0; i<qc.size(); i++)
  {
    hamilt.add(evalHamiltonian(qc.getUnchecked(i), pc.getUnchecked(i)));
    //cout << "H(" << i << ") = " << evalHamiltonian(qc.getUnchecked(i), pc.getUnchecked(i)) << endl;
  }
  
  // use trapezoidal rule to calculate action = integral(0, T, p•dq - H*dt)
  double newaction = 0.;
  juce::Array<double> cumul_action;
  cumul_action.add(0.);
  for (int i=0; i<qc.size()-1; i++)
  {
    //cout << "at step " << i << endl;
    double deltaTi = t.getUnchecked(i+1) - t.getUnchecked(i);
    //cout << "\tdelta Ti = " << deltaTi << endl;
    // integrad at i
    double integrand = -0.5 * (hamilt.getUnchecked(i) + hamilt.getUnchecked(i+1)) * deltaTi;
    //integrand = 0.;
    
    jassert(pc.getUnchecked(i).size() == pc.getUnchecked(i+1).size()); // safety check
    jassert(qc.getUnchecked(i).size() == qc.getUnchecked(i+1).size());
    double spdebug = 0.;
    for (int m=0; m<qc.getUnchecked(i).size(); m++)
    {
      spdebug = pc.getUnchecked(i).getUnchecked(m)*(qc.getUnchecked(i+1).getUnchecked(m)-qc.getUnchecked(i).getUnchecked(m));
      double sp = 0.5 * (pc.getUnchecked(i).getUnchecked(m) + pc.getUnchecked(i+1).getUnchecked(m)) * (qc.getUnchecked(i+1).getUnchecked(m)-qc.getUnchecked(i).getUnchecked(m));
      integrand += sp;
      //cout << "\t(sp)_" << m << " = 1/2 * (" << pc.getUnchecked(i+1).getUnchecked(m) << "+" << pc.getUnchecked(i).getUnchecked(m);
      //cout << " * (" << qc.getUnchecked(i+1).getUnchecked(m) << "-" << qc.getUnchecked(i).getUnchecked(m) << ")" << " = " << sp << endl;
    }
    //cout << "p•dq = " << spdebug << "\tH_i "<< " = " << hamilt.getUnchecked(i) << ". dt = " << deltaTi << ". integrand = " << integrand << endl;
    newaction += integrand;
    cumul_action.add(newaction);
    //cout << "\tadding " << integrand << endl;
  }
  
  //cout << "action = " << newaction << endl;
  // update action value
  //action = newaction;
  // keep track of action history
  //actionDescent.add(newaction);
  
  //return newaction;
  return cumul_action;
  
}




// using Méthod of Leapfrog / Störmer–Verlet instead of Euler Method
void NEPSolver::nextStepHamiltonEoM(StateVec& q, StateVec& p, double dt_in, const bool forward, bool& shouldStop, Trajectory & traj)
{
  if (shouldStop)
    return;
  
  double thrshold = 1000.;
  double dt = (forward ? dt_in : -1.*dt_in);
  
  // save initial q and p in case that next step should not occur
  StateVec qi = q;
  StateVec pi = p;
  
  StateVec gradqH = evalHamiltonianGradientWithQ(q, p);
  if (norm2(gradqH)>thrshold) // cancel this step, reset to initial conditions
  {
    q = qi;
    p = pi;
    shouldStop = true;
    return;
  }
  // update p
  for (int m=0; m<q.size(); m++)
    p.setUnchecked(m, p.getUnchecked(m) - 0.5*dt*gradqH.getUnchecked(m));
  
  // calculate gradients w.r.t to p
  StateVec gradpH = evalHamiltonianGradientWithP(q, p);
  
  if (norm2(gradpH)>thrshold)
  {
    q = qi;
    p = pi;
    shouldStop = true;
    return;
  }
  
  // update q
  for (int m=0; m<q.size(); m++)
    q.setUnchecked(m, q.getUnchecked(m) + dt*gradpH.getUnchecked(m));
  
  // update gradients w.r.t to q
  gradqH = evalHamiltonianGradientWithQ(q, p);
  if (norm2(gradqH)>thrshold)
  {
    q = qi;
    p = pi;
    shouldStop = true;
    return;
  }
  
  // update p once more
  for (int m=0; m<q.size(); m++)
    p.setUnchecked(m, p.getUnchecked(m) - 0.5*dt*gradqH.getUnchecked(m));
  
  // add new (q ; p) point to the trajectory
  PhaseSpaceVec psv;
  for (int m=0; m<q.size(); m++)
  {
    psv.add(q.getUnchecked(m));
  }
  for (int m=0; m<p.size(); m++)
  {
    psv.add(p.getUnchecked(m));
  }
  traj.add(psv);
  
}
