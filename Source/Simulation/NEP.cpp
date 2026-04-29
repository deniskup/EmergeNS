//  NEP.cpp
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//

#include "NEP.h"
#include "Simulation.h"
using namespace juce;

juce_ImplementSingleton(NEP);




double cartesianDistance(StateVec v1, StateVec v2)
{
  jassert(v1.size() == v2.size());
  double d = 0.;
  for (int k=0; k<v1.size(); k++)
  {
    d += (v2.getUnchecked(k)-v1.getUnchecked(k)) * (v2.getUnchecked(k)-v1.getUnchecked(k));
  }
  d = sqrt(d);
  return d;
}

double norm2(StateVec v)
{
  double norm = 0.;
  for (int k=0; k<v.size(); k++)
  {
    norm += v.getUnchecked(k) * v.getUnchecked(k);
  }
  norm = sqrt(norm);
  return norm;
}

double scalarProduct(StateVec v1, StateVec v2)
{
  jassert(v1.size() == v2.size());
  int n = v1.size();
  double sp = 0.;
  for (int k=0; k<n; k++)
    sp += v1.getUnchecked(k)*v2.getUnchecked(k);
  return sp;
}


double curveLength(const Curve c)
{
  double d = 0.;
  for (int k=0; k<c.size()-1; k++)
  {
    StateVec v = c.getUnchecked(k);
    StateVec vnext = c.getUnchecked(k+1);
    d += cartesianDistance(v, vnext);
  }
  return d;
}

bool areParallel(StateVec v1, StateVec v2, double tolerance, bool maxPrintingAllowed)
{
  if (v1.size() != v2.size())
    return false;
  
  double n1 = norm2(v1);
  double n2 = norm2(v2);
  
  if (n1 == 0. || n2 == 0.)
    return true;
  
  double sp = scalarProduct(v1, v2);
  
  double ratio = sp / (n1*n2);
  double epsilon = 1. - ratio;
  /*
  if (maxPrintingAllowed)
  {
    cout << "areCollinear function()" << endl;
    cout << "v1 = ";
    for (auto& el : v1)
      cout << el << " ";
    cout << endl;
    cout << "v2 = ";
    for (auto& el : v2)
      cout << el << " ";
    cout << endl;
    
    cout << "v1 • v2 = " << sp << endl;
    cout << "||v1|| x ||v2|| = " << n1*n2 << endl;
    cout << "epsilon = " << epsilon << endl;
  }
  */
    
  return (epsilon < tolerance);
  
}




dsp::Matrix<double> calculateLiftingJacobian_brutforce(EncapsVarForGSL& ev, StateVec p, double mu, const long int dim)
{
  dsp::Matrix<double> jaco(dim, dim);
  
  StateVec dHdp = ev.nep->evalHamiltonianGradientWithP(ev.qcenter, p);
  dsp::Matrix<double> hessian = ev.nep->evalHamiltonianHessianWithP(ev.qcenter, p);
  
  
  assert(dHdp.size() == dim-1);
  assert(hessian.getSize().getUnchecked(0) == dim-1);
  assert(hessian.getSize().getUnchecked(1) == dim-1);
  assert(ev.deltaq.size() == dim-1);
  assert(ev.equation_norm.size() == dim);
  assert(ev.pnorm.size() == dim-1);
  
  for (int i=0; i<dim; i++)
  {
    for (int j=0; j<dim; j++)
    {
      if (i==0)
      {
        if (j==dim-1)
          jaco(i, j) = 0.;
        else
          jaco(i, j) = dHdp.getUnchecked(j) / ev.equation_norm.getUnchecked(0);
      }
      else
      {
        if (j==dim-1)
        {
          double norm2_dq = norm2(ev.deltaq);
          jassert(norm2_dq);
          jaco(i, j) = -1. * ev.epsilon * mu * ev.deltaq.getUnchecked(i-1) / (norm2_dq * ev.equation_norm.getUnchecked(i));
        }
        else
        {
          jassert(ev.pnorm.getUnchecked(i-1) > 0.);
          jaco(i, j) = ev.epsilon * hessian(i-1, j) / (ev.pnorm.getUnchecked(i-1) * ev.equation_norm.getUnchecked(i));
        }
      }
    }
  }
  return jaco;
}




//dsp::Matrix<double> calculateLiftingJacobian(EncapsVarForGSL& ev, StateVec p, const long int nvar)
// dHdp must be properly normalized with respect to p when passed to this function
dsp::Matrix<double> calculateLiftingJacobian(StateVec dHdp, dsp::Matrix<double> hessian, dsp::Matrix<double> B, StateVec pnorm, StateVec equation_norm, long int nvar)
{
  long int nrows = nvar;
  long int ncol = nvar;
  dsp::Matrix<double> jaco(nrows, ncol);
  
  jassert(dHdp.size() == nvar);
  jassert(pnorm.size() == nvar);
  jassert(equation_norm.size() == nvar);
  jassert(hessian.getSize().getUnchecked(0) == nvar);
  jassert(hessian.getSize().getUnchecked(1) == nvar);
  for (int k=0; k<nvar; k++)
  {
    jassert(pnorm.getUnchecked(k)>0.);
    jassert(equation_norm.getUnchecked(k)>0.);
  }

  
  for (int i=0; i<nrows; i++)
  {
    for (int j=0; j<ncol; j++)
    {
      if (i==0)
      {
        jaco(i, j) = dHdp.getUnchecked(j) / equation_norm.getUnchecked(i);
      }
      else
      {
        double Jij = 0.;
        for (int k=0; k<nvar; k++)
        {
          Jij += B(i-1, k) * hessian(k, j) / pnorm.getUnchecked(k);
        }
        
        jaco(i, j) = Jij / equation_norm.getUnchecked(i);
      }
    }
  }
  return jaco;
}



 
 //In the following the system to solve is :
 //H(p,q) = 0
 //epsilon * ( dH/dp - e^s * dq / || dq || ) = 0
 
 
// x size = number of entities in the system + 1
int residual4GSL_brutforce(const gsl_vector* x, void* params, gsl_vector* f)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = ev->qcenter;
  StateVec dq = ev->deltaq;
  double norm2_dq = norm2(dq);
  assert(norm2_dq > 0.);
  Array<double> pnorm = ev->pnorm;
  
  const unsigned long n = x->size;
  
  for (int k=0; k<=n-1; k++)
    assert(ev->equation_norm.getUnchecked(k)>0.);

  // retrieve momentum and time
  StateVec p;
  for (int k=0; k<n-1; k++)
  {
    double pk = gsl_vector_get(x, k);
    p.add(pk);
  }
  double s = gsl_vector_get(x, n-1);
  double mu = exp(s);
  //double dt = exp(s); // force parameter to be strictly positive
  
  // calculate hamiltonian
  double H = ev->nep->evalHamiltonian(q, p);
  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  
  assert(dHdp.size() == n-1);
  assert(dq.size() == n-1);
  
  // set the non-linear equalitites to solve by gsl
  gsl_vector_set(f, 0., H / ev->equation_norm.getUnchecked(0));
  for (int k=1; k<=n-1; k++)
  {
    jassert(pnorm.getUnchecked(k-1) > 0.);
    double u = dHdp.getUnchecked(k-1) / pnorm.getUnchecked(k-1) - mu * dq.getUnchecked(k-1) / norm2_dq;
    u /= ev->equation_norm.getUnchecked(k);
    gsl_vector_set(f, k, u * ev->epsilon);
  }
  
  return GSL_SUCCESS;
}


// x size = number of entities in the system + 1
int residual4GSL_df_brutforce(const gsl_vector* x, void* params, gsl_matrix * J)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = ev->qcenter;
  StateVec dq = ev->deltaq;
  double norm2_dq = norm2(dq);
  assert(norm2_dq > 0.);
  Array<double> pnorm = ev->pnorm;
  
  const unsigned long n = x->size;
  
  for (int k=0; k<=n-1; k++)
    assert(ev->equation_norm.getUnchecked(k)>0.);

  // retrieve momentum and time
  StateVec p;
  for (int k=0; k<n-1; k++)
  {
    double pk = gsl_vector_get(x, k);
    p.add(pk);
  }
  //double dt = gsl_vector_get(x, n-1);
  double s = gsl_vector_get(x, n-1);
  double mu = exp(s);
  //double dt = exp(s);
  
  // calculate dH/dp
  //StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  
  // calculate d^2H/dp2 (hessian matrix w.r.t to p)
  //dsp::Matrix<double> d2Hd2p = ev->nep->evalHamiltonianHessianWithP(q, p);
  
  //assert(dHdp.size() == n-1);
  //assert(d2Hd2p.getSize().getUnchecked(0) == n-1);
  //assert(d2Hd2p.getSize().getUnchecked(1) == n-1);
  
  // set the jacobian elements associated to equations
  // H = 0
  // dH/dp - mu * dq / ||dq|| = 0
  dsp::Matrix<double> jaco = calculateLiftingJacobian_brutforce(*ev, p, mu, n);
  for (int i=0; i<n; i++)
  {
    for (int j=0; j<n; j++)
    {
      gsl_matrix_set(J, i, j, jaco(i,j));
    }
  }
  
  return GSL_SUCCESS;
}



// x size = number of entities in the system + 1
int residual4GSL_fdf_brutforce(const gsl_vector* x, void* params, gsl_vector* f, gsl_matrix * J)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = ev->qcenter;
  StateVec dq = ev->deltaq;
  double norm2_dq = norm2(dq);
  assert(norm2_dq > 0.);
  Array<double> pnorm = ev->pnorm;
  
  const unsigned long n = x->size;
  
  for (int k=0; k<=n-1; k++)
    assert(ev->equation_norm.getUnchecked(k)>0.);

  // retrieve momentum and time
  StateVec p;
  for (int k=0; k<n-1; k++)
  {
    double pk = gsl_vector_get(x, k);
    p.add(pk);
  }
  //double dt = gsl_vector_get(x, n-1);
  double s = gsl_vector_get(x, n-1);
  double mu = exp(s);
  
  // calculate hamiltonian
  double H = ev->nep->evalHamiltonian(q, p);
  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  // calculate d^2H/dp2 (hessian matrix w.r.t to p)
  //dsp::Matrix<double> d2Hd2p = ev->nep->evalHamiltonianHessianWithP(q, p);
  
  assert(dHdp.size() == n-1);
  //assert(d2Hd2p.getSize().getUnchecked(0) == n-1);
  //assert(d2Hd2p.getSize().getUnchecked(1) == n-1);
  
  // set the non-linear equalitites to solve by gsl
  gsl_vector_set(f, 0., H / ev->equation_norm.getUnchecked(0));
  for (int k=1; k<=n-1; k++)
  {
    jassert(pnorm.getUnchecked(k-1) > 0.);
    double u = dHdp.getUnchecked(k-1) / pnorm.getUnchecked(k-1) - mu * dq.getUnchecked(k-1) / norm2_dq;
    u /= ev->equation_norm.getUnchecked(k);
    gsl_vector_set(f, k, u * ev->epsilon);
  }
  
  // set the jacobian elements associated to equations
  // H = 0
  // dH/dp - mu * dq / ||dq|| = 0
  dsp::Matrix<double> jaco = calculateLiftingJacobian_brutforce(*ev, p, mu, n);
  for (int i=0; i<n; i++)
  {
    for (int j=0; j<n; j++)
    {
      gsl_matrix_set(J, i, j, jaco(i,j));
    }
  }
    
  return GSL_SUCCESS;
}


int residual4GSL(const gsl_vector* x, void* params, gsl_vector* f)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  const unsigned long nvar = x->size;
  
  StateVec q = ev->qcenter;
  Array<double> pnorm = ev->pnorm;
  
  jassert(q.size() == nvar);
  jassert(pnorm.size() == nvar);
  for (int k=0; k<nvar; k++)
  {
    assert(ev->pnorm.getUnchecked(k)>0.);
    assert(ev->equation_norm.getUnchecked(k)>0.);
  }
  jassert(ev->B.getNumRows() == nvar-1);
  jassert(ev->B.getNumColumns() == nvar);

  // retrieve momentum
  StateVec p;
  for (int k=0; k<nvar; k++)
  {
    double pk = gsl_vector_get(x, k);
    p.add(pk);
  }
  
  // calculate hamiltonian
  double H = ev->nep->evalHamiltonian(q, p);
  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  jassert(dHdp.size() == nvar);

  // set the non-linear equalitites to solve by gsl
  gsl_vector_set(f, 0., H / ev->equation_norm.getUnchecked(0));
  for (int k=0; k<ev->B.getNumRows() ; k++)
  {
    jassert(pnorm.getUnchecked(k) > 0.);
    double uk = 0.;
    for (int j=0; j<nvar; j++)
    {
      uk += ev->B(k, j) * dHdp.getUnchecked(j) / pnorm.getUnchecked(j);
    }
    uk /= ev->equation_norm.getUnchecked(k);
    gsl_vector_set(f, k+1, uk * ev->epsilon);
  }
  
  return GSL_SUCCESS;
}


// x size = number of entities in the system + 1
int residual4GSL_df(const gsl_vector* x, void* params, gsl_matrix * J)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = ev->qcenter;
  
  Array<double> pnorm = ev->pnorm;
  
  const unsigned long nvar = x->size;
  
  jassert(q.size() == nvar);
  jassert(pnorm.size() == nvar);
  for (int k=0; k<nvar; k++)
  {
    jassert(ev->equation_norm.getUnchecked(k)>0.);
    jassert(ev->pnorm.getUnchecked(k)>0.);
  }
  jassert(ev->B.getNumRows() == nvar-1);
  jassert(ev->B.getNumColumns() == nvar);

  // retrieve momentum
  StateVec p;
  for (int k=0; k<nvar; k++)
  {
    double pk = gsl_vector_get(x, k);
    p.add(pk);
  }
  
  // calculate gradient dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  
  // calculate hessian
  dsp::Matrix<double> hessian = ev->nep->evalHamiltonianHessianWithP(q, p);
  
  // set the jacobian elements associated to equations
  // H = 0
  // B • D-1 •  dH/dp = 0
  dsp::Matrix<double> jaco = calculateLiftingJacobian(dHdp, hessian, ev->B, ev->pnorm, ev->equation_norm, nvar);
  for (int i=0; i<nvar; i++)
  {
    for (int j=0; j<nvar; j++)
    {
      gsl_matrix_set(J, i, j, jaco(i,j));
    }
  }
  
  return GSL_SUCCESS;
}



// x size = number of entities in the system + 1
int residual4GSL_fdf(const gsl_vector* x, void* params, gsl_vector* f, gsl_matrix * J)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = ev->qcenter;
  Array<double> pnorm = ev->pnorm;
  
  const unsigned long nvar = x->size;
  
  jassert(q.size() == nvar);
  jassert(pnorm.size() == nvar);
  for (int k=0; k<nvar; k++)
  {
    assert(ev->pnorm.getUnchecked(k)>0.);
    assert(ev->equation_norm.getUnchecked(k)>0.);
  }
  jassert(ev->B.getNumRows() == nvar-1);
  jassert(ev->B.getNumColumns() == nvar);

  // retrieve momentum and time
  StateVec p;
  for (int k=0; k<nvar; k++)
  {
    double pk = gsl_vector_get(x, k);
    p.add(pk);
  }
  
  // calculate hamiltonian
  double H = ev->nep->evalHamiltonian(q, p);
  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  assert(dHdp.size() == nvar);
  
  // set the non-linear equalitites to solve by gsl
  gsl_vector_set(f, 0., H / ev->equation_norm.getUnchecked(0));
  for (int k=0; k<ev->B.getNumRows() ; k++)
  {
    jassert(pnorm.getUnchecked(k) > 0.);
    double uk = 0.;
    for (int j=0; j<nvar; j++)
    {
      uk += ev->B(k, j) * dHdp.getUnchecked(j) / pnorm.getUnchecked(j);
    }
    uk /= ev->equation_norm.getUnchecked(k);
    gsl_vector_set(f, k+1, uk * ev->epsilon);
  }
  
  // calculate hessian
  dsp::Matrix<double> hessian = ev->nep->evalHamiltonianHessianWithP(q, p);
  
  // set the jacobian elements associated to equations
  // H = 0
  // B • D-1 •  dH/dp = 0
  dsp::Matrix<double> jaco = calculateLiftingJacobian(dHdp, hessian, ev->B, ev->pnorm, ev->equation_norm, nvar);
  for (int i=0; i<nvar; i++)
  {
    for (int j=0; j<nvar; j++)
    {
      gsl_matrix_set(J, i, j, jaco(i,j));
    }
  }
    
  return GSL_SUCCESS;
}


///////////////////////////////////////////

int residual4GSL_opt(const gsl_vector* x, void* params, gsl_vector* f)
{
  
  // retrieve encapsulated variables
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  const unsigned long nvar = x->size;
  
  // retrieve q, dq and pborm for more readability
  StateVec q = ev->qcenter;
  StateVec dq = ev->deltaq;
  double dq_norm2 = norm2(dq);
  Array<double> pnorm = ev->pnorm;
  
  // some sanity checks
  jassert(dq_norm2>0.);
  jassert(q.size() == nvar);
  jassert(pnorm.size() == nvar);
  for (int k=0; k<nvar; k++)
  {
    assert(pnorm.getUnchecked(k)>0.);
    assert(ev->equation_norm.getUnchecked(k)>0.);
  }

  // retrieve momentum and normalize it
  StateVec p;
  for (int k=0; k<nvar; k++)
  {
    double pk = gsl_vector_get(x, k) * ev->pnorm.getUnchecked(k);
    p.add(pk);
  }
  
  double mu = exp(ev->s);
  
  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  jassert(dHdp.size() == nvar);

  // set the non-linear equalitites to solve by gsl
  for (int k=0; k<nvar ; k++)
  {
    jassert(pnorm.getUnchecked(k) > 0.);
    double uk = dHdp.getUnchecked(k) - mu * ev->deltaq.getUnchecked(k) / dq_norm2;
    //uk /= ev->equation_norm.getUnchecked(k);
    gsl_vector_set(f, k, uk);
  }
  
  return GSL_SUCCESS;
}


// x size = number of entities in the system + 1
int residual4GSL_df_opt(const gsl_vector* x, void* params, gsl_matrix * J)
{
  
  // retrieve encapsulated variables
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  const unsigned long nvar = x->size;
  
  // retrieve q, dq and pborm for more readability
  StateVec q = ev->qcenter;
  StateVec dq = ev->deltaq;
  double dq_norm2 = norm2(dq);
  Array<double> pnorm = ev->pnorm;
  
  // some sanity checks
  jassert(dq_norm2>0.);
  jassert(q.size() == nvar);
  jassert(pnorm.size() == nvar);
  for (int k=0; k<nvar; k++)
  {
    assert(pnorm.getUnchecked(k)>0.);
    assert(ev->equation_norm.getUnchecked(k)>0.);
  }

  // retrieve momentum
  StateVec p;
  for (int k=0; k<nvar; k++)
  {
    double pk = gsl_vector_get(x, k) * ev->pnorm.getUnchecked(k);
    p.add(pk);
  }
  
  // calculate hessian
  dsp::Matrix<double> hessian = ev->nep->evalHamiltonianHessianWithP(q, p);
  
  // set the jacobian elements associated to equations
  // d2H/dp2 = 0
  for (int i=0; i<nvar; i++)
  {
    for (int j=0; j<nvar; j++)
    {
      gsl_matrix_set(J, i, j, hessian(i,j) * ev->pnorm.getUnchecked(j));
    }
  }
  
  return GSL_SUCCESS;
}



// x size = number of entities in the system + 1
int residual4GSL_fdf_opt(const gsl_vector* x, void* params, gsl_vector* f, gsl_matrix * J)
{
  
  
  // retrieve encapsulated variables
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  const unsigned long nvar = x->size;
  
  // retrieve q, dq and pborm for more readability
  StateVec q = ev->qcenter;
  StateVec dq = ev->deltaq;
  double dq_norm2 = norm2(dq);
  Array<double> pnorm = ev->pnorm;
  
  // some sanity checks
  jassert(dq_norm2>0.);
  jassert(q.size() == nvar);
  jassert(pnorm.size() == nvar);
  for (int k=0; k<nvar; k++)
  {
    assert(pnorm.getUnchecked(k)>0.);
    assert(ev->equation_norm.getUnchecked(k)>0.);
  }

  // retrieve momentum
  StateVec p;
  for (int k=0; k<nvar; k++)
  {
    double pk = gsl_vector_get(x, k) * ev->pnorm.getUnchecked(k);
    p.add(pk);
  }
  
  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  jassert(dHdp.size() == nvar);
  
  double mu = exp(ev->s);

  // set the non-linear equalitites to solve by gsl
  for (int k=0; k<nvar ; k++)
  {
    jassert(pnorm.getUnchecked(k) > 0.);
    double uk = dHdp.getUnchecked(k) - mu * ev->deltaq.getUnchecked(k) / dq_norm2;
    uk /= ev->equation_norm.getUnchecked(k);
    gsl_vector_set(f, k, uk);
  }
  
  // calculate hessian
  dsp::Matrix<double> hessian = ev->nep->evalHamiltonianHessianWithP(q, p);
  
  // set the jacobian elements associated to equations
  // d2H/dp2 = 0
  for (int i=0; i<nvar; i++)
  {
    for (int j=0; j<nvar; j++)
    {
      gsl_matrix_set(J, i, j, hessian(i,j) * pnorm.getUnchecked(j) );
    }
  }
    
  return GSL_SUCCESS;
}




double residual4GSL_mu_opt(double x, void* params)
{
  
  // retrieve encapsulated variables
  EncapsVarForGSL_MU * ev = static_cast<EncapsVarForGSL_MU*>(params);
    
  // calculate H
  double H = ev->nep->evalHamiltonian(ev->q, ev->p); // p depends on mu
  
  return H;

}


double residual4GSL_mu_df_opt(double x, void* params)
{
  
  // retrieve encapsulated variables
  EncapsVarForGSL_MU * ev = static_cast<EncapsVarForGSL_MU*>(params);
  
  double mu = exp(x);
  
  // calculate hessian
  dsp::Matrix<double> hessian = ev->nep->evalHamiltonianHessianWithP(ev->q, ev->p);
  // pass hessian to Eigen
  Eigen::MatrixXd eigen_hessian(hessian.getNumRows(), hessian.getNumColumns());
  for (int i=0; i<hessian.getNumRows(); i++)
  {
    for (int j=0; j<hessian.getNumColumns(); j++)
    {
      eigen_hessian(i, j) = hessian(i, j);
    }
  }
  
  int dim = ev->dq.size();
  jassert(eigen_hessian.rows() == dim);
  jassert(eigen_hessian.cols() == dim);
  jassert(ev->dq_norm2 > 0.);
  
  
  // build target vector
  Eigen::VectorXd b(dim);
  for (int k=0; k<dim; k++)
    b[k] =  ev->dq.getUnchecked(k)/ev->dq_norm2;
  
  // Solve the equation hessian * a = b in a using Cholesky decomposition methods (hessian is positive semi-definite)
  Eigen::LLT<Eigen::MatrixXd> lltOfHessian(eigen_hessian);
  Eigen::VectorXd a = lltOfHessian.solve(b);
  
  double derivative = mu*mu;
  derivative *= a.adjoint() * b;
  
  return derivative;
  
}



// x size = number of entities in the system + 1
void residual4GSL_mu_fdf_opt(double x, void * params, double * y, double * dy)
{
  // retrieve encapsulated variables
  EncapsVarForGSL_MU * ev = static_cast<EncapsVarForGSL_MU*>(params);
  
  // retrieve mu
  double mu = exp(x);
  
  // calculate H
  double H = ev->nep->evalHamiltonian(ev->q, ev->p);
  
  // calculate hessian
  dsp::Matrix<double> hessian = ev->nep->evalHamiltonianHessianWithP(ev->q, ev->p);
  // pass hessian to Eigen
  Eigen::MatrixXd eigen_hessian(hessian.getNumRows(), hessian.getNumColumns());
  for (int i=0; i<hessian.getNumRows(); i++)
  {
    for (int j=0; j<hessian.getNumColumns(); j++)
    {
      eigen_hessian(i, j) = hessian(i, j);
    }
  }
  
  int dim = ev->dq.size();
  jassert(eigen_hessian.rows() == dim);
  jassert(eigen_hessian.cols() == dim);
  jassert(ev->dq_norm2 > 0.);
  
  // build target vector
  Eigen::VectorXd b(dim);
  for (int k=0; k<dim; k++)
    b[k] =  ev->dq.getUnchecked(k)/ev->dq_norm2;
  
  // Solve the equation hessian * a = b in a using Cholesky decomposition methods (hessian is positive semi-definite)
  Eigen::LLT<Eigen::MatrixXd> lltOfHessian(eigen_hessian);
  Eigen::VectorXd a = lltOfHessian.solve(b);
  
  double derivative = mu*mu;
  derivative *= a.adjoint() * b;
  
  *y = H;
  *dy = derivative;

}



// using legendre fetchel inpired method
double residual4GSL_LF(const gsl_vector *x, void *params)
{
  
  // retrieve encapsulated variables
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return std::numeric_limits<double>::infinity();;
  }
  const unsigned long nvar = x->size;
  
  
  // retrieve q, dq and pborm for more readability
  StateVec q = ev->qcenter;
  StateVec dq = ev->deltaq;
  double dq_norm2 = norm2(dq);
  Array<double> pnorm = ev->pnorm;
  

  
  // some sanity checks
  jassert(dq_norm2>0.);
  jassert(q.size() == nvar);
  jassert(pnorm.size() == nvar);
  for (int k=0; k<nvar; k++)
  {
    assert(pnorm.getUnchecked(k)>0.);
  }
  


  // retrieve momentum and normalize it
  StateVec p;
  for (int k=0; k<nvar; k++)
  {
    double pk = gsl_vector_get(x, k);// * ev->pnorm.getUnchecked(k);
    p.add(pk);
  }
  
  double mu = exp(ev->s);
  
  // calculate dH/dp
  double H = ev->nep->evalHamiltonian(q, p);

  // set the non-linear equalitites to solve by gsl
  double sp = 0.;
  for (int k=0; k<nvar ; k++)
  {
    sp +=  ev->deltaq.getUnchecked(k) * p.getUnchecked(k);
  }
  sp *= mu / dq_norm2;
  
  
  return  (H - sp);
}


// x size = number of entities in the system
void residual4GSL_df_LF(const gsl_vector* x, void* params, gsl_vector *df)
{

  
  // retrieve encapsulated variables
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->qcenter.size() == 0 || ev->deltaq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return;
  }
  const unsigned long nvar = x->size;
  
  // retrieve q, dq and pborm for more readability
  StateVec q = ev->qcenter;
  StateVec dq = ev->deltaq;
  double dq_norm2 = norm2(dq);
  Array<double> pnorm = ev->pnorm;
  
  // some sanity checks
  jassert(dq_norm2>0.);
  jassert(q.size() == nvar);
  jassert(pnorm.size() == nvar);
  for (int k=0; k<nvar; k++)
  {
    assert(pnorm.getUnchecked(k)>0.);
  }

  // retrieve momentum
  StateVec p;
  for (int k=0; k<nvar; k++)
  {
    double pk = gsl_vector_get(x, k);// * ev->pnorm.getUnchecked(k);
    p.add(pk);
  }
  double mu = exp(ev->s);
  
  // calculate dH/dp
  StateVec dHdp = ev->nep->evalHamiltonianGradientWithP(q, p);
  jassert(dHdp.size() == nvar);
  
  // set derivative
  for (int k=0; k<nvar; k++)
  {
    double dk = dHdp.getUnchecked(k) - mu * dq.getUnchecked(k) / dq_norm2;
    gsl_vector_set(df, k, dk);
  }
  
  
  return;
}



// x size = number of entities in the system
void residual4GSL_fdf_LF(const gsl_vector *x, void *params, double *f, gsl_vector *df)
{
  
  *f = residual4GSL_LF(x, params);
  residual4GSL_df_LF(x, params, df);
}




 

//////////////////////////////////////////////////////////////////////////////////////////////////


NEP::NEP() : ControllableContainer("NEP"),
            Thread("NEP"),
            simul(Simulation::getInstance()),
            nepNotifier(1000)
{
  
  
  //showWarningInUI = true;
 // saveAndLoadRecursiveData = true;
  //includeInRecursiveSave = true;
  

  
  // affect satID to entities
  simul->affectSATIds();
  
  startDescent = addTrigger("Start Descent", "Start action functionnal descent algorithm");
  
  stopDescent = addTrigger("Stop Descent", "Manually stop the descent algorithm");
  test = addTrigger("test", "");
  
  //start_heteroclinic_study = addTrigger("Heteroclinic study", "Produces most probable trajectories between two fixed points");
    
  // enum parameters = steady states
  sst_stable = addEnumParameter("Stable steady state", "Choose stable fixed point to start the NEP algorithm from");
  sst_saddle = addEnumParameter("Unstable steady state", "Choose unstable fixed point to start the NEP algorithm from");
  
  Niterations = addIntParameter("Max. iterations", "Maximum of iterations the descent will perform", 10);
  
  nPoints_start = addIntParameter("Sampling points", "Number of sampling points used for the descent", 10);
  
  nPoints_max = addIntParameter("Max. sampling", "Maximum number of sampling points used by the descent", 100);
  
  initialConditions = addEnumParameter("Initial condition", "Choose how the optimal trajectory is initialized for the descent.");

  //cutoffFreq = addFloatParameter("Cutoff frequency", "Cutoff frequency normalized to a sampling rate of 1", 0.05);

  //maxcutoffFreq = addFloatParameter("Max. cutoff frequency", "max. frequency of low-pass filtering, after what descent will stop.", 100.);
  
  solverType = addEnumParameter("Solver type", "Solver lib. and method to use for the descent");
  
  action_threshold = addStringParameter("Action threshold", "Descent will stop when action threshold is reached", "1e-5");
  
  //timescale_factor = addFloatParameter("Time scale factor", "Descent behaves badly when kinetics rate constants are too low. A solution consists in scaling up those constants.", 100.);
  
  stepDescentInitVal = addFloatParameter("Initial step descent", "Descent will try proceeding with user indicated step, and will decrease it following the use of a backtracking method if this step is too large.", 1.);
  
  maxPrinting = addBoolParameter("Maximum Printing", "Will print whole descent in a DEBUG.TXT file.", false);
    
  // set options
  updateSteadyStateList();
  
  initialConditions->clearOptions();
  initialConditions->addOption("Straigth line", 0);
  initialConditions->addOption("Deterministic trajectory", 1);
  
  solverType->clearOptions();
  solverType->addOption("GSL Brut force - NLS", 0);
  solverType->addOption("GSL Decouple t/p - NLS", 1);
  solverType->addOption("GSL Decouple t/p - Minimizer", 2);

  
  // set this class as simulation listener
  //simul->addAsyncSimulationListener(this);
  //simul->addAsyncContainerListener(this);
  
  kinetics = new KineticLaw(false, 0.);
  
  try
  {
    size_t pos;
    d_action_threshold = std::stod(action_threshold->stringValue().toStdString(), &pos);
    if (pos != action_threshold->stringValue().toStdString().size())
    {
      LOGWARNING("action_threshold invalid double, setting to 1e-5 by default");
      d_action_threshold = 1e-5;
    }
    
  } catch (const std::invalid_argument& s) {
    LOGWARNING("action_threshold invalid double, setting to 1e-5 by default");
    d_action_threshold = 1e-5;
  }
 

  
}



NEP::~NEP()
{
  //simul->removeAsyncSimulationListener(this);
  //simul->removeAsyncContainerListener(this);
}


void NEP::updateSteadyStateList()
{
  // set options
  sst_stable->clearOptions();
  sst_saddle->clearOptions();
  for (int k=0; k<simul->steadyStatesList->arraySteadyStates.size(); k++)
  {
    SteadyState sst = simul->steadyStatesList->arraySteadyStates.getUnchecked(k);
    if (sst.isBorder)
      continue;
    
    if (sst.isStable)
      sst_stable->addOption(String(k), k);
    else if (!sst.isStable)
      sst_saddle->addOption(String(k), k);
  }
  
}


void NEP::onContainerParameterChanged(Parameter *p)
{
  if (p == action_threshold)
  {
    try
    {
      size_t pos;
      d_action_threshold = std::stod(action_threshold->stringValue().toStdString(), &pos);
      if (pos != action_threshold->stringValue().toStdString().size())
      {
        LOGWARNING("action_threshold invalid double, setting to 1e-5 by default");
        d_action_threshold = 1e-5;
      }
      
    } catch (const std::invalid_argument& s) {
      LOGWARNING("action_threshold invalid double, setting to 1e-5 by default");
      d_action_threshold = 1e-5;
    }
    cout << "NEW ACTION THRESHOLD = " << d_action_threshold << endl;
  }
  
}


void NEP::onContainerTriggerTriggered(Trigger* t)
{
  if (t == startDescent)
  {
    stopThread(10);
    state = Descending;
    startThread();
  }
  else if (t == start_heteroclinic_study)
  {
    heteroclinic_study = true;
    stopThread(10);
    startThread();
  }
  else if (t == stopDescent)
  {
    stop();
  }
  else if (t == test)
  {
    //StateVec v = {1., 1., 1.};
    //dsp::Matrix<double> hh = buildOrthogonalBasis(v);
    debuggingFunction();
  }
}



void NEP::onChildContainerRemoved(ControllableContainer* cc)
{
  
}


double NEP::evalHamiltonian(const StateVec q, const StateVec p)
{
  //cout << "--- hamiltonian calculation --- " << endl;
  double H = 0.;
    
  jassert(p.size() == q.size());
  if (p.size() != q.size())
    return H;
  
  Array<double> vecH;
  for (auto & reaction : Simulation::getInstance()->reactions)
  {
    if (!reaction->enabled)
      continue;
    //cout << reaction->name << endl;
    // forward reaction
    double forward = reaction->assocRate;
    double sp1 = 0.;
    double pow1 = 1.;
    for (auto & ent : reaction->reactants)
    {
      sp1 -= p.getUnchecked(ent->idSAT);
      pow1 *= q.getUnchecked(ent->idSAT);
    }
    for (auto & ent : reaction->products)
      sp1 += p.getUnchecked(ent->idSAT);
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
      sp2 += p.getUnchecked(ent->idSAT);
    for (auto & ent : reaction->products)
    {
      sp2 -= p.getUnchecked(ent->idSAT);
      pow2 *= q.getUnchecked(ent->idSAT);
    }
    backward *= (exp(sp2) - 1.) * pow2;
    H += backward;
    
    //cout << "spbackward = " << sp2 << endl;
    //cout << "q^nu backward = " << pow2 << endl;
    //cout << "Hbackward = " << backward << endl;
    
    //cout << "current H = " << H << endl;
    
    vecH.add(H);
    
  } // end loop over reactions
  
  // loop over creation/destruction reactions,
  // formally treated as 0 <--> entity
  for (auto & ent : simul->entities)
  {
    double creat = ent->creationRate * ( exp(p.getUnchecked(ent->idSAT)) - 1. );
    H += creat;
    
    double dest = ent->destructionRate * ( exp(-1.*p.getUnchecked(ent->idSAT)) - 1. ) * q.getUnchecked(ent->idSAT);
    H += dest;
  }
  
  
  /*
  cout << "--- hamiltonian check --- " << endl;
  for (int k=0; k<vecH.size(); k++)
  {
    cout << "H" << k << " = " << vecH.getUnchecked(k) << endl;
  }
  cout << "Htot = " << H << endl;
  */
  
  return timescale_factor * H;
}




StateVec NEP::evalHamiltonianGradientWithP(const StateVec q, const StateVec p)
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
  int dim = simul->entities.size();
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
  for (auto & reaction : Simulation::getInstance()->reactions)
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
    Array<double> thisgrad;
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
  for (auto & ent : simul->entities)
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
    gradpH.setUnchecked(m, gradpH.getUnchecked(m)*timescale_factor);
  
  return gradpH;
}



dsp::Matrix<double> NEP::evalHamiltonianHessianWithP(const StateVec q, const StateVec p)
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
  int dim = simul->entities.size();
  dsp::Matrix<double> nullmatrix(dim, dim);
  nullmatrix.clear(); // Fills the contents of the matrix with zeroes.
  dsp::Matrix hess(nullmatrix);
  
  
  jassert(p.size() == q.size());
  if (p.size() != q.size())
    return nullmatrix;
    
  
    // loop over reactions
    for (auto & reaction : Simulation::getInstance()->reactions)
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
    for (auto & ent : simul->entities)
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
        hess(i, j) *= timescale_factor;
      }
    }
    
    return hess;
  
}




StateVec NEP::evalHamiltonianGradientWithQ(const StateVec q, const StateVec p)
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
  int dim = simul->entities.size();
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
  for (auto & reaction : Simulation::getInstance()->reactions)
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
  for (auto & ent : simul->entities)
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
    gradqH.setUnchecked(m, gradqH.getUnchecked(m)*timescale_factor);

  return gradqH;
  
}


void NEP::reset()
{
  // reset previous calculations
  actionDescent.clear();
  trajDescent.clear();
  dAdqDescent.clear();
  dAdqDescent_filt.clear();
  gslStatus_descent.clear();
  collinearityStatus_descent.clear();
  residuals_H_descent.clear();
  residuals_p_descent.clear();
  
  g_qcurve.clear();
  g_pcurve.clear();
  g_times.clear();
  dAdq.clear();
  dAdq_filt.clear();
  action = 10.;
  length_qcurve = 0.;
  stepDescent = stepDescentInitVal->floatValue();
  stepDescentInit_dynamic = stepDescentInitVal->floatValue();
  //cutoffFreq->setValue(0.05);
  nPoints = nPoints_start->intValue();
  tolerance_mu = tolerance_mu_init;
}


void NEP::stop()
{
  state = Idle;
  LOG("Descent algorithm stops");
  signalThreadShouldExit();
}



// start thread
void NEP::run()
{
  simul->affectSATIds();
  reset();

  // has bad behavior for now, trajectory eventually diverges
  // need deeper understanding
  // see https://web.pa.msu.edu/people/dykman/pub06/jcp100_5735.pdf
  if (heteroclinic_study)
  {
    LOG("heteroclinic study not implemented yet, return.");
    return;
    //heteroclinicStudy();
    //heteroclinic_study = false;
  }

  
  if (maxPrinting->boolValue())
  {
    system("mkdir -p debug");
    cout << "WILL DO MAX PRINTINGS" << endl;
    debugfile.open("./debug/DEBUG.txt", ofstream::out | ofstream::trunc);
    debugfile << "\t\t\t------ DEBUG ------" << endl;
    debugfile << "Descent parameters" << endl;
    debugfile << "Sampling points : " << nPoints_max->intValue() << endl;
    //debugfile << "Max. sampling : " << nPoints_max->intValue() << endl;
  }
  
  // init concentration curve
  LOG("init g_qcurve");
  try
  {
    initConcentrationCurve();
  } catch (const std::exception& e)
  {
    LOGWARNING(e.what());
    return;
  }
  
  // message to async
  nepNotifier.addMessage(new NEPEvent(NEPEvent::WILL_START, this));
  
  // set normalisation factor in order to have all kinetic constants of order 1
  setTimeNormalizationFactor();
  LOG("Using time normalization factor : " + to_string(timescale_factor));
  
  
  // start descent
  int count = 0;
  while (descentShouldContinue(count+1) && !threadShouldExit())
  {
    count++;
    LOG("\niteration #" + to_string(count-1));
    
    if (count>1)
    {
      LOG("Using backtracking method...");
      stepDescent = backTrackingMethodForStepSize(g_qcurve);
      LOG("using step = " + to_string(stepDescent));
      updateOptimalConcentrationCurve(g_qcurve, stepDescent);
    }
    
    if (maxPrinting->boolValue())
    {
      debugfile << "\nIteration " << count << endl;
      debugfile << "-- concentration curve --" << endl;
      debugfile << "[ ";
      for (int p=0; p<g_qcurve.size(); p++)
      {
        debugfile << "(";
        int c=0;
        for (auto & qm : g_qcurve.getUnchecked(p))
        {
          string closebracket = (p == g_qcurve.size()-1 ? ") " : "), ");
          string comma = (c == g_qcurve.getUnchecked(p).size()-1 ? closebracket : ",");
          debugfile << qm << comma ;
          c++;
        }
      }
      debugfile << " ]" << endl;
    }
    
    // lift current trajectory to full (q ; p; t) space
    // this function updates global variables g_pcurve and times
    LOG("lifting trajectory");
    //LiftTrajectoryOptResults liftoptres = liftCurveToTrajectoryWithNLOPT();
    LiftTrajectoryOptResults liftoptres = liftCurveToTrajectoryWithGSL(g_qcurve, true);
    
    // for NEPUI
    double successFrac = 0.;
    double d_npoints = (double) nPoints - 1.;
    jassert(d_npoints>0.);
    for (int k=0; k<liftoptres.gslStatus.size()-1; k++)
    {
     if (liftoptres.gslStatus.getUnchecked(k) == 1)
       successFrac += 1. / d_npoints;
    }
    if (isinf(successFrac) || isnan(successFrac))
      successFrac = 0.;
    successFrac *= 100.;
    cout << "Convergence Fraction = " << successFrac << "%" << endl;
    
    // update global variable with lift results
    g_pcurve = liftoptres.pcurve;
    g_times = liftoptres.times;
    
    // keep track of trajectory update in (q ; p) space
    Trajectory newtraj;
    Array<double> hams;
    for (int point=0; point<nPoints; point++)
    {
      PhaseSpaceVec psv;
      for (auto & qm : g_qcurve.getUnchecked(point))
        psv.add(qm);
      for (auto & pm : g_pcurve.getUnchecked(point))
        psv.add(pm);
      newtraj.add(psv);
      hams.add(evalHamiltonian(g_qcurve.getUnchecked(point), g_pcurve.getUnchecked(point))); 
    }
    //cout << "adding a trajectory of size : " << newtraj.size() << " = " << g_qcurve.size() << " + " << g_pcurve.size() << endl;
    trajDescent.add(newtraj);
    
    // keep track of gsl convergence status
    gslStatus_descent.add(liftoptres.gslStatus);
    collinearityStatus_descent.add(liftoptres.collinearity);
    
    // Keep track of residuals
    residuals_H_descent.add(liftoptres.residuals_H);
    residuals_p_descent.add(liftoptres.residuals_p);
    
    /*
    if (maxPrinting->boolValue())
    {
      debugfile << "-- momentum curve --" << endl;
      debugfile << "[ ";
      for (int p=0; p<nPoints; p++)
      {
        debugfile << "(";
        int c=0;
        for (auto & pm : g_pcurve.getUnchecked(p))
        {
          string closebracket = (p == nPoints-1 ? ") " : "), ");
          string comma = (c == g_pcurve.getUnchecked(p).size()-1 ? closebracket : ",");
          debugfile << pm << comma ;
          c++;
        }
      }
      debugfile << " ]" << endl;
      debugfile << "-- time sampling --" << endl;
      debugfile << "[ ";
      //cout << "times.size = " << g_times.size() << endl;
      for (int p=0; p<nPoints; p++)
      {
        string comma = (p == nPoints-1 ? "" : ", ");
        debugfile << g_times.getUnchecked(p) << comma ;
      }
      debugfile << " ]" << endl;
    }
    */
  
    
    // calculate action value
    LOG("calculating action");
    Array<double> newcumulaction = calculateAction(g_qcurve, g_pcurve, g_times);
    double newaction = newcumulaction.getLast();
    double diffAction = action - newaction;
    LOG("action = " + to_string(newaction));
    
    if (isnan(newaction)|| isnan(diffAction))
    {
      LOGWARNING("Action is nan. Descent probably diverged. Stopping descent.");
      signalThreadShouldExit();
    }
    
    if (newaction<0.)
    {
      LOGWARNING("Action is <0. Probably wrong. Stopping descent.");
      signalThreadShouldExit();
    }
      
    actionDescent.add(newcumulaction);
    action = newaction;
    
    if (maxPrinting->boolValue())
    {
      debugfile << "-- Action --" << endl;
      debugfile << "S = " << newaction << " & deltaS = " << diffAction << endl;
    }
    
    //LOG("action = " + to_string(newaction) + ". deltaS = " + to_string(diffAction));
    
    // message to async to monitor the descent
    double dummy_cutoffFreq = 1.;
    nepNotifier.addMessage(new NEPEvent(NEPEvent::NEWSTEP, this, count, newaction, dummy_cutoffFreq, nPoints, metric, successFrac));
    
    
    // check algorithm descent status
    bool shouldUpdate = descentShouldUpdateParams(diffAction);
    if (shouldUpdate && count>1)
    {
      LOG("descentUpdatesParams");
      updateDescentParams();
      
      // resample the concentration and momentum curves
      //resampleInSpaceUniform(g_qcurve, nPoints);
      //canUpdateConcentrationCurve = false;
      
      // problem if I just continue : the descent will not save same size elements (actions, dAdq...)
      //continue;
      
      // the following I do not perfor
      //resampleInTimeUniform(g_qcurve, g_qcurve.size());
      //lowPassFiltering(g_qcurve, true);
      //resampleInSpaceUniform(g_qcurve, g_qcurve.size());
      //liftCurveToTrajectoryWithGSL();
      
    }
    
    
    // functional gradient dA / dq
    for (int point=0; point<nPoints; point++)
    {
      StateVec dHdqk = evalHamiltonianGradientWithQ(g_qcurve.getUnchecked(point), g_pcurve.getUnchecked(point));
      StateVec dpdtk;
      dpdtk.insertMultiple(0, 0., nPoints);
      if (point>0 && point<(nPoints-1))
      {
        for (int m=0; m<dHdqk.size(); m++)
        {
          double dpm = liftoptres.opt_momentum.getUnchecked(point).getUnchecked(m) - liftoptres.opt_momentum.getUnchecked(point-1.).getUnchecked(m);
          double dtm = 0.5*(liftoptres.opt_deltaT.getUnchecked(point) + liftoptres.opt_deltaT.getUnchecked(point-1));
          dpdtk.setUnchecked(m, dpm/dtm);
        }
      }
      //cout << "point " << point << endl;
      StateVec dAdqk;
      for (int m=0; m<dHdqk.size(); m++)
      {
        dAdqk.add(-dHdqk.getUnchecked(m) - dpdtk.getUnchecked(m));
        //cout << "\t" << -dHdqk.getUnchecked(m) << " " << - dpdtk.getUnchecked(m) << endl;
      }
      
      dAdq.add(dAdqk);
    }
    dAdqDescent.add(dAdq);
    
    // filter gradient
    dAdq_filt = dAdq;
    //lowPassFiltering(dAdq_filt, false);
    //dAdqDescent_filt.add(dAdq_filt);
   
    if (maxPrinting->boolValue())
    {
      debugfile << "-- dAdq --" << endl;
      debugfile << "[ ";
      for (int p=0; p<nPoints; p++)
      {
        debugfile << "(";
        StateVec dAdqk = dAdq.getUnchecked(p);
        int c=0;
        for (auto & coord : dAdqk)
        {
          string closebracket = (p == nPoints-1 ? ") " : "), ");
          string comma = ( c==dAdqk.size()-1 ? closebracket : "," );
          debugfile << coord << comma;
          c++;
        }
      }
      debugfile << " ]" << endl;
    }
        
  } // end while
  
  //cout << actionDescent.size() << " --- " << trajDescent.size() << endl;
  
  if (maxPrinting)
  {
    debugfile.close();
  }
  
  // save descent algorithm results into a file
  LOG("writing descent to file");
  writeDescentToFile();
  
  //stop();
  
  
}


// uses Householder algorithm to build an orthogonal basis of space orthogonal to input vector v
// argument : some non-normalized input vector
dsp::Matrix<double> NEP::buildOrthogonalBasis(StateVec v)
{
  int dim = v.size();
  if (dim == 0)
  {
    dsp::Matrix<double> dummy(0, 0);
    return dummy;
  }
  
  // init output matrix with null matrix
  dsp::Matrix<double> household(dim-1, dim);
  for (int i=0; i<household.getNumRows(); i++)
  {
    for (int j=0; j<household.getNumColumns(); j++)
    {
      household(i,j) = 0.;
    }
  }
  
  double v_norm2 = norm2(v);
  if (v_norm2 == 0.)
    return household;
  
  // normalize input vector
  StateVec vnorm(v);
  for (int k=0; k<vnorm.size(); k++)
    vnorm.setUnchecked(k, vnorm.getUnchecked(k)/v_norm2);
  
  // pick dimension where input vector has lower value
  int argmin = 0;
  double min = 10.;
  for (int k=0; k<vnorm.size(); k++)
  {
    if (abs(vnorm.getUnchecked(k))<min)
    {
      argmin = k;
      min = vnorm.getUnchecked(k);
    }
  }
  
  // build referent vector from whom to build the orthogonal basis
  // u = (v - e_argmin) / || v - e_argmin || with e_argmin = (0...1...0) contains a 1 only at index argmin
  StateVec u(vnorm);
  u.setUnchecked(argmin, u.getUnchecked(argmin) - 1);
  double u_norm2 = norm2(u);
  jassert(u_norm2>0.);
  for (int k=0; k<u.size(); k++)
  {
    u.setUnchecked(k, u.getUnchecked(k)/u_norm2); // normalize u to 1
  }
  
  // Build matrix that projects e_argmin on v and the rest in orthogonal space to v
  dsp::Matrix<double> Q(dim, dim);
  for (int i=0; i<dim; i++)
  {
    for (int j=0; j<dim; j++)
    {
      double deltaij = i==j ? 1. : 0.;
      double uij = u.getUnchecked(i) * u.getUnchecked(j);
      double qij = deltaij - 2. * uij;
      Q(i,j) = qij;
    }
  }
  
  // fill the household matrix
  int icorr = -1;
  for (int i=0; i<dim; i++) // lines
  {
    if (i==argmin) // skip line corresponding to i == argmin
      continue;
    icorr++;
    for (int j=0; j<dim; j++) // col
    {
      double element = Q(j,i);
      household(icorr, j) = element; // check that this is fine
    }
  }
  /*
  cout << "input vector v = ";
  for (auto & el : v)
    cout << el << " ";
  cout << endl;
  
  cout << "Build household basis with referent dimension = " << argmin << endl;
  
  cout << "\nhousehold matrix : " << endl;
  for (int i=0; i<household.getNumRows(); i++)
  {
    for (int j=0; j<household.getNumColumns(); j++)
    {
      cout << household(i, j) << " ";
    }
    cout << endl;
  }
  
  cout << "\n";
  for (int i=0; i<household.getNumRows(); i++)
  {
    StateVec bi;
    for (int j=0; j<household.getNumColumns(); j++)
    {
      bi.add(household(i,j));
    }
    double spi = scalarProduct(v, bi);
    cout << "b_" << i << " • v = " << spi << endl;
  }
  */
  
  return household;
}




// arguments
// n : dimension of the problem to solve = number of entities + 1
// gsl_status_previous_point : gsl status of the previous point, used as initial guess of set to true
gsl_vector * NEP::initialOptimalGuess_brutforce(const int n, const bool gsl_status_previous_point, vector<double> previous_gsl_result, const StateVec qcenter)
{
  gsl_vector* x = gsl_vector_alloc(n);
  
  if (gsl_status_previous_point)
  {
    // p
    StateVec pinit;
    for (int m=0; m<n-1; m++)
    {
      double pm = 0.1;
      gsl_vector_set(x, m, pm);
      pinit.add(pm);
    }
    // dt = (dq•dH/dp) / || dH/dp ||^2
    StateVec dHdp = evalHamiltonianGradientWithP(qcenter, pinit);
    double norm2 = 0.;
    double sp = 0.;
    for (int m=0; m<pinit.size(); m++)
    {
      norm2 += dHdp.getUnchecked(m)*dHdp.getUnchecked(m);
      sp += qcenter.getUnchecked(m)*dHdp.getUnchecked(m);
    }
    norm2 = sqrt(norm2);
    double dtinit = 1.;
    if (norm2>0.)
      dtinit = abs(sp) / norm2;
    else
      
      gsl_vector_set(x, n-1, dtinit);
  }
  else
  {
    // use results of previous optimization point
    for (int k=0; k<n; k++)
      gsl_vector_set(x, k, previous_gsl_result[k]);
  }
  
  return x;
  
}



// arguments
// n : dimension of the problem to solve = number of entities
// gsl_status_previous_point : gsl status of the previous point, used as initial guess of set to true
gsl_vector * NEP::initialOptimalGuess(const int n, const bool gsl_status_previous_point, vector<double> previous_gsl_result, const StateVec qcenter)
{
  gsl_vector* x = gsl_vector_alloc(n);
  
  if (!gsl_status_previous_point)
  {
    // p
    StateVec pinit;
    for (int m=0; m<n; m++)
    {
      double pm = 0.1;
      gsl_vector_set(x, m, pm);
      pinit.add(pm);
    }
  }
  else
  {
    // use results of previous optimization point
    for (int k=0; k<n; k++)
      gsl_vector_set(x, k, previous_gsl_result[k]);
  }
  
  //cout << "pinit = ";
  //for (int k=0; k<n; k++)
  //  cout << gsl_vector_get(x, k) << " ";
  //cout << endl;
  
  return x;
  
}

// Performs the actual multivariate solving. Arguments :
// s : the gsl multiroot solver used
// fdf : the multivariate vector function for which gsl will attempt to find roots
// ev : home-made encapsulated variables to pass to gsl for the solving
int NEP::gslMultirootSolving_brutforce(gsl_multiroot_fdfsolver * s, gsl_multiroot_function_fdf & fdf, EncapsVarForGSL & ev, bool useContinuation)
{
  // continuation of the system
  // solve H(p, q) = 0 and epsilon * { dH(p,q)/dq - dp/dt } = 0 for increasing values of epsilon
  double epsilon = 0.1;
  int status = GSL_CONTINUE;
  int iter = 0;
  int maxiter = 100;
  double tolerance = tolerance_mu_min;
  
  int emax = 1;
  if (useContinuation)
    emax = 9;
  
  for (int e=0; e<emax; e++)
  {
    if (!useContinuation)
      epsilon = 1.;
    
    // update parameters in multiroot function
    ev.epsilon = epsilon;
    fdf.params = &ev;
    iter = 0;
    status = GSL_CONTINUE;
    //cout << "\tepsilon = " << epsilon << endl;
    
    // set initial guess to output of previous iteration
    gsl_vector * xprev = s->x;
    gsl_multiroot_fdfsolver_set(s, &fdf, xprev);
    
    while (status == GSL_CONTINUE && iter <= maxiter)
    {
      iter++;
      //cout << "\titer" << iter << endl;
      //status = gsl_multiroot_fsolver_iterate(s); // if I'm using the jacobian gsl_multiroot_fdfsolver_iterate
      status = gsl_multiroot_fdfsolver_iterate(s); // returns GSL_SUCCESS if the iteration went good
      if (status != GSL_SUCCESS)
        break;
      status = gsl_multiroot_test_residual(s->f, tolerance); // returns GSL_SUCCESS if converged, GSL_CONTINUE otherwise
      double norm2 = 0.;
      for (int k=0; k<s->f->size; k++)
        norm2 += gsl_vector_get(s->f, k)*gsl_vector_get(s->f, k);
      norm2 = sqrt(norm2);
      //cout << "\tresidual : " << norm2 << endl;
    }
    //std::cout << "\tstatus = " << gsl_strerror(status) << "\n";
    if (!useContinuation)
      break;
    epsilon += 1./10.;
  }
  
  
  int outstatus = status == GSL_SUCCESS ? 1 : 0;

  return outstatus;
}


// make sure to have dHdp parallel to dq, not anti-parallel.
// If antiparallel, apply p = p* + dp with dp = Hess-1 ( (v • dHdp) v - dHdp(p*) )
// and v = dq / ||dq||
// argument :
// gsl_vector s->x : current vector state within gsl solver
// EncapsVarForGSL& ev
void NEP::correctMomentumDirectionIfFollowingWrongBranch(gsl_vector& x, StateVec q, StateVec dq)
{
  //cout << "NEP::correctMomentumDirectionIfFollowingWrongBranch()" << endl;
  
  // Retrieve momentum
  StateVec p;
  for (int k=0; k<x.size; k++)
    p.add(gsl_vector_get(&x, k));
  // calculate dHdp
  StateVec dHdp = evalHamiltonianGradientWithP(q, p);
  
  //cout << "current p = ";
  //for (auto & el : p)
  //  cout << el << " ";
  //cout << endl;
  
  double norm2_dq = norm2(dq);
  if (norm2_dq == 0.)
    return;
  
  // calculate dHdp • v
  double sp = 0.;
  for (int k=0; k<dq.size(); k++)
    sp += dq.getUnchecked(k) * dHdp.getUnchecked(k);
  sp /= norm2_dq;
  
  //cout << "dHdp • v = " << sp << endl;;
  
  if (sp < 0.)
  {
    // calculate Hessian and invert it
    dsp::Matrix<double> hessian =evalHamiltonianHessianWithP(q, p);
    // copy matrix into eigen oriented matrix
    Eigen::MatrixXd eig_hessian(hessian.getNumRows(), hessian.getNumColumns());
    for (int i=0; i<eig_hessian.rows(); i++)
    {
      for (int j=0; j<eig_hessian.cols(); j++)
      {
        eig_hessian(i, j) = hessian(i, j);
      }
    }
    // invert
    Eigen::MatrixXd eig_inv_hessian = eig_hessian.inverse();
    
    // check if some elements of the inverse are nan or inf, in this case the inversion did not work
    bool isValid = true;
    for (int i=0; i<eig_inv_hessian.rows(); i++)
    {
      for (int j=0; j<eig_inv_hessian.cols(); j++)
      {
        if (isinf(eig_inv_hessian(i,j)) || isnan(eig_inv_hessian(i,j)))
        {
          isValid = false;
          break;
        }
      }
    }
    if (!isValid)
      return;
    /*
    cout << "hess = " << endl;
    for (int i=0; i<eig_hessian.rows(); i++)
    {
      for (int j=0; j<eig_hessian.cols(); j++)
      {
        cout << eig_hessian(i, j) << " ";
      }
      cout << endl;
    }
    
    cout << "hess^(-1) = " << endl;
    for (int i=0; i<eig_inv_hessian.rows(); i++)
    {
      for (int j=0; j<eig_inv_hessian.cols(); j++)
      {
        cout << eig_inv_hessian(i, j) << " ";
      }
      cout << endl;
    }
    */
    
    // calculate dp component wise
    StateVec dp;
    dp.insertMultiple(0, 0., p.size());
    for (int i=0; i<p.size(); i++)
    {
      double pi = 0.;
      for (int j=0; j<p.size(); j++)
      {
        pi += eig_inv_hessian(i, j) * ( abs(sp)*dq.getUnchecked(j)/norm2_dq - dHdp.getUnchecked(j));
      }
      dp.setUnchecked(i, pi);
    }
    
    //cout << "dp = ";
    //for (auto & el : dp)
    //  cout << el << " ";
    //cout << endl;
    
    // update gsl_vector
    for (int i=0; i<x.size; i++)
    {
      gsl_vector_set(&x, i, p.getUnchecked(i) + dp.getUnchecked(i));
    }
    
  } // end if sp < 0
  
  return;
}


// Performs the actual multivariate solving. Arguments :
// s : the gsl multiroot solver used
// fdf : the multivariate vector function for which gsl will attempt to find roots
// ev : home-made encapsulated variables to pass to gsl for the solving
int NEP::gslMultirootSolving(gsl_multiroot_fdfsolver * s, gsl_multiroot_function_fdf & fdf, EncapsVarForGSL & ev, bool useContinuation)
{
  // continuation of the system
  // solve H(p, q) = 0 and epsilon * { dH(p,q)/dq - dp/dt } = 0 for increasing values of epsilon
  double epsilon = 0.1;
  int status = GSL_CONTINUE;
  int iter = 0;
  int maxiter = 100;
  double tolerance = 1e-6;
  
  int emax = 1;
  if (useContinuation)
    emax = 9;
  
  for (int e=0; e<emax; e++)
  {
    if (!useContinuation)
      epsilon = 1.;
    
    // update parameters in multiroot function
    ev.epsilon = epsilon;
    fdf.params = &ev;
    iter = 0;
    status = GSL_CONTINUE;
    //cout << "\tepsilon = " << epsilon << endl;
    
    // set initial guess to output of previous iteration
    gsl_vector * xprev = s->x;
    gsl_multiroot_fdfsolver_set(s, &fdf, xprev);
    
    while (status == GSL_CONTINUE && iter <= maxiter)
    {
      iter++;
      
      correctMomentumDirectionIfFollowingWrongBranch(*s->x, ev.qcenter, ev.deltaq);
      /*
      // make sure to have dHdp parallel to dq
      StateVec p;
      for (int k=0; k<s->x->size; k++)
        p.add(gsl_vector_get(s->x, k));
      StateVec dHdp = evalHamiltonianGradientWithP(ev.qcenter, p);
      double sp = 0.;
      for (int k=0; k<ev.deltaq.size(); k++)
        sp += ev.deltaq.getUnchecked(k) * dHdp.getUnchecked(k);
      if (sp>0.)
      {
        for (int k=0; k<ev.deltaq.size(); k++)
          ev.deltaq.setUnchecked(k, -1.*ev.deltaq.getUnchecked(k));
      }
      */
      
      //status = gsl_multiroot_fsolver_iterate(s); // if I'm using the jacobian gsl_multiroot_fdfsolver_iterate
      status = gsl_multiroot_fdfsolver_iterate(s); // returns GSL_SUCCESS if the iteration went good
      if (status != GSL_SUCCESS)
        break;
      status = gsl_multiroot_test_residual(s->f, tolerance); // returns GSL_SUCCESS if converged, GSL_CONTINUE otherwise
      //double norm2 = 0.;
      //for (int k=0; k<s->f->size; k++)
      //  norm2 += gsl_vector_get(s->f, k)*gsl_vector_get(s->f, k);
      //norm2 = sqrt(norm2);
      //cout << "\tresidual : " << norm2 << endl;
    }
    //std::cout << "\tstatus = " << gsl_strerror(status) << "\n";
    if (!useContinuation)
      break;
    epsilon += 1./10.;
  }
      
  status = ( status == GSL_SUCCESS? 1 : 0);

  return status;
}





// Performs the actual multivariate solving. Arguments :
// s : the gsl multiroot solver used
// fdf : the multivariate vector function for which gsl will attempt to find roots
// ev : home-made encapsulated variables to pass to gsl for the solving
int NEP::gslMultirootSolving_opt(gsl_multiroot_fdfsolver * s_p, gsl_root_fdfsolver* s_mu, gsl_multiroot_function_fdf & fdf_p, gsl_function_fdf& fdf_mu, EncapsVarForGSL & ev_p, EncapsVarForGSL_MU & ev_mu)
{
  // continuation of the system
  int iter_mu = 0;
  int iter_p = 0;
  int maxiter = 100;
  double tolerance = 1e-8;
  double tolerance_mu = 1e-8;
  double residual_mu = 1000.;
  
  int gslstatus_p = GSL_CONTINUE;
  int gslstatus_mu = GSL_CONTINUE;
  
  // iteration on mu
  while (gslstatus_mu == GSL_CONTINUE && iter_mu <= maxiter)
  {
    iter_mu++;
    gslstatus_p = GSL_CONTINUE;
    
    // set initial guess to output of previous iteration
    //gsl_vector * xprev = s_p->x;
    //gsl_multiroot_fdfsolver_set(s_p, &fdf, xprev);
    
    iter_p = 0;
    
    // iteration on p, solve dH/dp = mu * dq / ||dq||
    while (gslstatus_p == GSL_CONTINUE && iter_p <= maxiter)
    {
      iter_p++;
      //gslstatus = gsl_multiroot_fsolver_iterate(s); // if I'm using the jacobian gsl_multiroot_fdfsolver_iterate
      gslstatus_p = gsl_multiroot_fdfsolver_iterate(s_p); // returns GSL_SUCCESS if the iteration went good
      if (gslstatus_p != GSL_SUCCESS)
        break;
      gslstatus_p = gsl_multiroot_test_residual(s_p->f, tolerance); // returns GSL_SUCCESS if converged, GSL_CONTINUE otherwise
    }
    //std::cout << "\tstatus = " << gsl_strerror(status) << "\n";
    
    if (gslstatus_p != GSL_SUCCESS)
    {
      //LOGWARNING("gsl not able to solve momentum problem. Stopping here.");
      break;
    }
    
    // retrieve current momentum
    StateVec currentP;
    currentP.insertMultiple(0, 0., (int)s_p->x->size);
    for (int k=0; k<s_p->x->size; k++)
      currentP.setUnchecked(k, gsl_vector_get(s_p->x, k));
    
    
    // pass its value to solver in mu
    ev_mu.p = currentP;
    fdf_mu.params = &ev_mu;
    gsl_root_fdfsolver_set(s_mu, &fdf_mu, s_mu->root);
    
    
    // calculate H
    //double H = evalHamiltonian(ev.qcenter, currentP);
    
    // hessian
    //dsp::Matrix<double> hessian = evalHamiltonianHessianWithP(ev.qcenter, currentP);
    
    // update mu value with a single iteration
    if (residual4GSL_mu_df_opt(s_mu->root, &ev_mu) != 0.)
      gslstatus_mu = gsl_root_fdfsolver_iterate(s_mu);
    else
    {
      // mu = dHdp • v / ||v||^2
      StateVec p;
      for (int k=0; k<s_p->x->size; k++)
        p.add(gsl_vector_get(s_p->x, k));
      StateVec dHdp = evalHamiltonianGradientWithP(ev_p.qcenter, p);
      double mu = abs(scalarProduct(dHdp, ev_p.deltaq));
      double n2 = norm2(ev_p.deltaq);
      jassert(n2>0.);
      if (n2>0.)
        mu /= (n2*n2);
      s_mu->root = log(mu);
      //cout << "smooth update on mu as phi'(mu)=0 : " << mu <<  " and s = " << s_mu->root << endl;
    }
    
    if (gslstatus_mu != GSL_SUCCESS)
    {
      //LOGWARNING("Iteration on mu variable went wrong. Quit.");
      break;
    }
    
    // pass mu value to solver in p
    double root_estimate = s_mu->root;
    ev_p.s = root_estimate;
    fdf_p.params = &ev_p;
    gsl_multiroot_fdfsolver_set(s_p, &fdf_p, s_p->x);
    
    // residual on mu
    residual_mu = GSL_FN_FDF_EVAL_F(s_mu->fdf, root_estimate);
    gslstatus_mu = gsl_root_test_residual(residual_mu, tolerance_mu);
    
    //cout << "\niter_mu : " << iter_mu << ". mu = " << exp(root_estimate) << ". residual_mu = " << residual_mu << endl;
    //cout << "p = ";
    //for (auto& el : currentP)
    //  cout << el << " ";
    //cout << endl;
    
    // update residual on mu
    //residual_mu = H;
    
    //if (residual_mu > tolerance_mu)
    //  newtonstatus = 0;
    
  }
  /*
  cout << "\n--- Convergence status --- " << endl;
  cout << "Niterations (p, mu) = (" << iter_p << " , " << iter_mu << ")" << endl;
  cout << "on P : " << gsl_strerror(gslstatus_p) << endl;
  cout << "on mu : " << gsl_strerror(gslstatus_mu) << endl;
  
  cout << "--- roots ---" << endl;
  cout << "p = ";
  for (int k=0; k<s_p->x->size; k++)
    cout << gsl_vector_get(s_p->x, k) << " ";
  cout << endl << "mu = " << s_mu->root << endl;
  
  cout << "--- Residuals --- " << endl;
  cout << "p_res = ";
  for (int k=0; k<s_p->f->size; k++)
    cout << gsl_vector_get(s_p->f, k) << " ";
  cout << "\nmu_res = " << residual_mu << endl;
  
  cout << "--- Jacobian --- " << endl;
  cout << "J = ";
  StateVec currentP;
  for (int k=0; k<s_p->x->size; k++)
    currentP.add(gsl_vector_get(s_p->x, k));
  dsp::Matrix<double> hess = evalHamiltonianHessianWithP(ev_p.qcenter, currentP);
  for (int i=0; i<hess.getNumRows(); i++)
  {
    for (int j=0; j<hess.getNumColumns(); j++)
    {
      cout << hess(i, j) << "\t";
    }
    cout << endl;
  }
  */
  
  // should solve a final time for p !!

    
  int globalStatus = ( gslstatus_p == GSL_SUCCESS && gslstatus_mu == GSL_SUCCESS ? 1 : 0);


  return globalStatus;
}



int NEP::solveForMomentumAtFixedMu(gsl_multimin_fdfminimizer * s_p, EncapsVarForGSL& ev_p, double tolerance_p)
{
  int iter_p = 0;
  int maxiter_p = 100;
  int gslstatus_p = GSL_CONTINUE;

  while (gslstatus_p == GSL_CONTINUE && iter_p <= maxiter_p)
  {
    iter_p++;
    gslstatus_p = gsl_multimin_fdfminimizer_iterate(s_p);
    
    if (gslstatus_p != GSL_SUCCESS)
      break;
    
    //gslstatus_p = gsl_multimin_test_gradient(s_p->gradient, 1e-3);
    //gslstatus_p = test_convergence_colinear_method();
    
    // dHdp and dq should be colinear, use this as a convergence criteria
    StateVec currentP;
    currentP.insertMultiple(0, 0., (int) s_p->x->size);
    for (int k=0; k<s_p->x->size; k++)
      currentP.setUnchecked(k,  gsl_vector_get(s_p->x, k));
    StateVec dHdp_opt = evalHamiltonianGradientWithP(ev_p.qcenter, currentP);
    bool bc = areParallel(dHdp_opt, ev_p.deltaq, tolerance_p, false);
    
    if (bc)
      gslstatus_p = GSL_SUCCESS;
    else
      gslstatus_p = GSL_CONTINUE;
  }
  
  return gslstatus_p;
}


// Performs the actual multivariate solving. Arguments :
// s : the gsl multiroot solver used
// fdf : the multivariate vector function for which gsl will attempt to find roots
// ev : home-made encapsulated variables to pass to gsl for the solving
int NEP::gslMultirootSolving_LF(gsl_multimin_fdfminimizer * s_p, gsl_root_fdfsolver* s_mu, gsl_multimin_function_fdf & fdf_p, gsl_function_fdf& fdf_mu, EncapsVarForGSL & ev_p, EncapsVarForGSL_MU & ev_mu)
{
  
  //cout << "gslMultirootSolving_LF()" << endl;
  
  // continuation of the system
  int iter_mu = 0;
  int maxiter_mu = 100;
  double tolerance_mu = tolerance_mu_init;
    
  int gslstatus_p = GSL_CONTINUE;
  int gslstatus_mu = GSL_CONTINUE;
  
  StateVec p_save;
  p_save.insertMultiple(0, 0., (int) s_p->x->size);
  for (int k=0; k<s_p->x->size; k++)
    p_save.setUnchecked(k, gsl_vector_get(s_p->x, k));

  double residual_mu = evalHamiltonian(ev_p.qcenter, p_save);
  double tolerance_p = min(abs(residual_mu), 1e-3);
  
  // iteration on mu
  while (gslstatus_mu == GSL_CONTINUE && iter_mu <= maxiter_mu)
  {
    //cout << "iter_mu = " << iter_mu << endl;
    
    iter_mu++;
    gslstatus_p = GSL_CONTINUE;
    
    // set initial guess to output of previous iteration
    //gsl_vector * xprev = s_p->x;
    //gsl_multiroot_fdfsolver_set(s_p, &fdf, xprev);
        
    // iteration on p, solve dH/dp = mu * dq / ||dq||
    gslstatus_p = solveForMomentumAtFixedMu(s_p, ev_p, tolerance_p);
    
    if (gslstatus_p != GSL_SUCCESS) // smooth update on mu
    {
      // mu = dHdp • v / ||v||^2
      StateVec p;
      for (int k=0; k<s_p->x->size; k++)
        p.add(gsl_vector_get(s_p->x, k));
      StateVec dHdp = evalHamiltonianGradientWithP(ev_p.qcenter, p);
      double mu = abs(scalarProduct(dHdp, ev_p.deltaq));
      double n2 = norm2(ev_p.deltaq);
      jassert(n2>0.);
      if (n2>0.)
        mu /= (n2*n2);
      
      // update mu in p solver and skip to next iteration in mu directly
      ev_p.s = log(mu);
      s_mu->root = log(mu);
      //cout << "smooth update on mu as failed in p : " << mu << " and s = " << ev_p.s << endl;
      continue;
    }
    else // keep track of momentum and reset failure counter
    {
      for (int k=0; k<p_save.size(); k++)
        p_save.setUnchecked(k, gsl_vector_get(s_p->x, k));
    }
    
    // retrieve current momentum
    StateVec currentP;
    currentP.insertMultiple(0, 0., (int)s_p->x->size);
    for (int k=0; k<s_p->x->size; k++)
      currentP.setUnchecked(k, gsl_vector_get(s_p->x, k));
    
    // printing
    //StateVec v1 = evalHamiltonianGradientWithP(ev_p.qcenter, currentP);
    //StateVec v2 = ev_p.deltaq;
    //double sp = scalarProduct(v1, v2);
    //double ratio = sp / (norm2(v1)*norm2(v2));
    //double epsilon = 1. - ratio;
    //cout << "iter_p : " << iter_p << ". epsilon = " << epsilon << ". statusP : " << gsl_strerror(gslstatus_p) << endl;
    
    
    // pass momentum value to solver in mu
    ev_mu.p = currentP;
    fdf_mu.params = &ev_mu;
    gsl_root_fdfsolver_set(s_mu, &fdf_mu, s_mu->root);
    
    // update mu value with a single iteration
    if (residual4GSL_mu_df_opt(s_mu->root, &ev_mu) != 0.)
      gslstatus_mu = gsl_root_fdfsolver_iterate(s_mu);
    else
    {
      // mu = dHdp • v / ||v||^2
      StateVec p;
      for (int k=0; k<s_p->x->size; k++)
        p.add(gsl_vector_get(s_p->x, k));
      StateVec dHdp = evalHamiltonianGradientWithP(ev_p.qcenter, p);
      double mu = abs(scalarProduct(dHdp, ev_p.deltaq));
      double n2 = norm2(ev_p.deltaq);
      jassert(n2>0.);
      if (n2>0.)
        mu /= (n2*n2);
      s_mu->root = log(mu);
      //cout << "smooth update on mu as phi'(mu)=0 : " << mu <<  " and s = " << s_mu->root << endl;
    }
    
    if (gslstatus_mu != GSL_SUCCESS)
    {
      //LOGWARNING("Iteration on mu variable went wrong. Quit.");
      break;
    }
    
    // pass mu value to solver in p
    double root_estimate = s_mu->root;
    ev_p.s = root_estimate;
    fdf_p.params = &ev_p;
    gsl_multimin_fdfminimizer_set(s_p, &fdf_p, s_p->x, 0.01, 1e-4);

    // residual on mu
    residual_mu = GSL_FN_FDF_EVAL_F(s_mu->fdf, root_estimate);
    if (abs(residual_mu) < tolerance_mu)
      gslstatus_mu = GSL_SUCCESS;
    else
      gslstatus_mu = GSL_CONTINUE;
    
    
    // decrease tolerance in p
    if (abs(residual_mu) <tolerance_p)
      tolerance_p = abs(residual_mu);
    
    //int test = gsl_root_test_residual(residual_mu, tolerance_mu);
    
    //gslstatus_mu = gsl_root_test_residual(residual_mu, tolerance_mu);
    
    
    //cout << ". mu = " << exp(root_estimate) << ". residual_mu = " << residual_mu << endl;
    //cout << gsl_strerror(gslstatus_mu) << " vs. " << gsl_strerror(test) << endl;
    
    //cout << "p = ";
    //for (auto& el : currentP)
    //  cout << el << " ";
    //cout << endl;
    
    // update residual on mu
    //residual_mu = H;
    
    //if (residual_mu > tolerance_mu)
    //  newtonstatus = 0;
    
  } // end loop on mu
  /*
  cout << "\n--- Convergence status --- " << endl;
  cout << "Niterations (p, mu) = (" << iter_p << " , " << iter_mu << ")" << endl;
  cout << "on P : " << gsl_strerror(gslstatus_p) << endl;
  cout << "on mu : " << gsl_strerror(gslstatus_mu) << endl;
  
  cout << "--- roots ---" << endl;
  cout << "p = ";
  for (int k=0; k<s_p->x->size; k++)
    cout << gsl_vector_get(s_p->x, k) << " ";
  cout << endl << "mu = " << exp(s_mu->root) << endl;
  
  cout << "--- Residuals --- " << endl;
  cout << "mu_res = " << residual_mu << endl;
  cout << "grad_p = ";
  for (int k=0; k<s_p->gradient->size; k++)
    cout << " " << gsl_vector_get(s_p->gradient, k);
  cout << endl;
  */
  
  // last resolution on p
  gslstatus_p = solveForMomentumAtFixedMu(s_p, ev_p, tolerance_p);
    
  int globalStatus = ( gslstatus_p == GSL_SUCCESS && gslstatus_mu == GSL_SUCCESS ? 1 : 0);


  return globalStatus;
}
















void printLiftingJacobian_brutforce(gsl_multiroot_fdfsolver * s, EncapsVarForGSL ev, int n)
{
  StateVec p;
  for (int i=0; i<n-1; i++)
  {
    p.add(gsl_vector_get(s->x, i));
  }
  double mu = exp(gsl_vector_get(s->x, n-1));
  
  dsp::Matrix<double> jaco = calculateLiftingJacobian_brutforce(ev, p, mu, n);
  
  cout << "J = " << endl;
  for (int i=0; i<n; i++)
  {
    for (int j=0; j<n; j++)
    {
      cout << jaco(i, j) << " ";
    }
    cout << endl;
  }
}

void printLiftingJacobian(gsl_multiroot_fdfsolver * s, EncapsVarForGSL ev, int n)
{
  StateVec p;
  for (int i=0; i<n; i++)
  {
    p.add(gsl_vector_get(s->x, i));
  }
  
  StateVec q = ev.qcenter;
  StateVec dHdp = ev.nep->evalHamiltonianGradientWithP(q, p);
  dsp::Matrix<double> hessian = ev.nep->evalHamiltonianHessianWithP(q, p);
  
  dsp::Matrix<double> jaco = calculateLiftingJacobian(dHdp, hessian, ev.B, ev.pnorm, ev.equation_norm, n);
  
  cout << "--- Jacobian ---" << endl;
  cout << "J = " << endl;
  for (int i=0; i<jaco.getNumRows(); i++)
  {
    for (int j=0; j<jaco.getNumColumns(); j++)
    {
      cout << jaco(i, j) << " ";
    }
    cout << endl;
  }
  
}


// argument n : dimension of the non-linear equations to resolve
LiftTrajectoryOptResults NEP::findOptimalMomentumAndTime_brutforce(const Curve& qcurve, const int n, bool maxPrintingAllowed)
{
  Array<double> vec_dt; // vector of optimal time assigned between each q(i) and q(i+1)
  Array<StateVec> vec_pstar; // vector of optimal momenta assigned between each q(i) and q(i+1)
  
  // keep track if GSL converged or not.
  Array<int> gslStatus;
  Array<int> convergenceSanityCheck;
  
  // residuals
  Array<double> residuals_H;
  Array<Array<double>> residuals_p;
  
  bool gsl_status_previous_point = false;
  vector<double> previous_gsl_result(n, 0.1);
  // loop over points in concentration space
  // q : q0 -- p*_0 -- q1 -- p*_1 --  .. -- qi -- p*_i -- q(i+1) -- p*_(i+1) -- ...
  for (int point=0; point<nPoints-1; point++) // n - 1 iterations
  {
    //cout << "qcurve point #" << k << endl;
    
    // calculate q, dq of current concentration curve
    StateVec q = qcurve.getUnchecked(point);
    StateVec qnext = qcurve.getUnchecked(point+1);
    jassert(q.size() == qnext.size());
    StateVec qcenter;
    Array<double> deltaq;
    for (int m=0; m<q.size(); m++)
    {
      deltaq.add(qnext.getUnchecked(m) - q.getUnchecked(m));
      qcenter.add( 0.5* (q.getUnchecked(m) + qnext.getUnchecked(m)));
    }
    
    // encaps useful variables to pass to GSL
    EncapsVarForGSL ev;
    ev.qcenter = qcenter;
    ev.deltaq = deltaq;
    ev.nep = this;
    ev.epsilon = 1.;
    
    // momentum normalization initialized to unity
    Array<double> pnorm;
    pnorm.insertMultiple(0, 1., n-1);
   // if (gsl_status_previous_point)
   // {
    //  for (int m=0; m<n-1; m++)
    //  {
    //    if (gsl_vector_get(x, m) != 0.)
    //      pnorm.setUnchecked(m, abs(gsl_vector_get(x, m)));
    //  }
    //}
    ev.pnorm = pnorm;
    
    // equation normalization
    Array<double> eqnorm;
    eqnorm.insertMultiple(0, 1., n);
    ev.equation_norm = eqnorm;
    
    // initial value for p and dt = || dq || / exp(s)
    // x = (p, s)
    gsl_vector* x = initialOptimalGuess_brutforce(n, gsl_status_previous_point, previous_gsl_result, qcenter);
    
    
    
    // init the gsl function and its derivatives
    gsl_multiroot_function_fdf fdf; // using jacobian
    fdf.f = residual4GSL_brutforce;
    fdf.df = residual4GSL_df_brutforce;
    fdf.fdf = residual4GSL_fdf_brutforce; // combines function to evaluate and the jacobian
    fdf.n = n;
    fdf.params = &ev;
    
    // init gsl solver withtout derivative
    const gsl_multiroot_fdfsolver_type * T = gsl_multiroot_fdfsolver_hybridj;
    gsl_multiroot_fdfsolver * s = gsl_multiroot_fdfsolver_alloc(T, n);
    gsl_multiroot_fdfsolver_set(s, &fdf, x);
    
    // actual solving
    bool useContinuation = true;
    int status = gslMultirootSolving_brutforce(s, fdf, ev, useContinuation);
    
    /*
    // if not successful, try again normalizing the momenta variable with current state of the solver
    if (status != GSL_SUCCESS)
    {
      LOG("Renormalizing momentum variables and equations !!");
      
      if (maxPrintingAllowed)
      {
        
        cout << "residual : ";
        for (int i=0; i<n; i++)
          cout << gsl_vector_get(s->f, i) << " ";
        cout << endl;
        
        cout << "J = " << endl;
        for (int i=0; i<n; i++)
        {
          for (int j=0; j<n; j++)
          {
            cout << gsl_matrix_get(s->J, i, j) << " ";
          }
          cout << endl;
        }
        
      }
      
      // update momentum normalization
      StateVec pprime;
      for (int m=0; m<n-1; m++)
      {
        double pm = gsl_vector_get(s->x, m);
        if (pm != 0.)
          ev.pnorm.setUnchecked(m, abs(pm));
        else
          ev.pnorm.setUnchecked(m, 1e-5);
        
        pprime.add(pm/ev.pnorm.getUnchecked(m));
        gsl_vector_set(s->x, m, pm/ev.pnorm.getUnchecked(m));
      }
      cout << "pnorm = ";
      for (auto & pm : ev.pnorm)
        cout << pm << " ";
      cout << endl;
      
      
      // to normalize equations
      StateVec equation_norm;

      // use jacobian norm2 of matrix line vector 'i' to normalize equation 'i'.
      for (int i=0; i<n; i++)
      {
        StateVec line;
        for (int j=0; j<n; j++)
        {
          if (i==0 && j == n-1) // this element is always 0, do not count it in renormalization
            continue;
          double jaco_ij = gsl_matrix_get(s->J, i, j);
          if (i>0 && j<n-1)
          {
            jaco_ij /= pnorm.getUnchecked(i); // update jacobian elements  taking into account renormalization of p
            //gsl_matrix_set(s->J, i, j, jaco_ij);
          }
          line.add(jaco_ij);
        }
        double si = norm2(line);
        if (si==0.)
          si = 1e-5;
        equation_norm.add(si);
      }
      
      cout << "eq norm : ";
      for (auto & e : equation_norm)
        cout << e << " ";
      cout << endl;
      
      // pass equation normalization to encapsulating variable
      ev.equation_norm = equation_norm;
  
      
      // calling again the multiroot solver
      useContinuation = false;
      status = gslMultirootSolving_brutforce(s, fdf, ev, useContinuation);
    }
    */

    // keep track of gsl status for current point
    gslStatus.add(status);
  

    //std::cout << "p0 = " << gsl_vector_get(s->x, 0) << "\n";
    //std::cout << "p1 = " << gsl_vector_get(s->x, 1) << "\n";
    //std::cout << "dt = " << gsl_vector_get(s->x, 1) << "\n";
    //cout << "used " << iter << " iterations" << endl;
    
    // keep track of residuals
    residuals_H.add(gsl_vector_get(s->f, 0));
    Array<double> rp;
    for (int k=1; k<s->f->size; k++)
      rp.add(gsl_vector_get(s->f, k));
    jassert(rp.size() == simul->entities.size());
    residuals_p.add(rp);
    
    //cout << "residuals = ";
    //for (int k=0; k<s->f->size; k++)
    //  cout << gsl_vector_get(s->f, k) << " ";
    //cout << endl;
    
    // retrieve results in a non-GSL form
    StateVec pstar;
    StateVec ptild;
    for (int m=0; m<n-1; m++)
    {
      pstar.add(gsl_vector_get(s->x, m) * ev.pnorm.getUnchecked(m));
      ptild.add(gsl_vector_get(s->x, m));
    }
    //double dt = gsl_vector_get(s->x, n-1);
    double last = gsl_vector_get(s->x, n-1);
    double mu = exp(last);
    //assert(mu != 0.);
    double deltaq_norm2 = norm2(deltaq);
    assert(deltaq_norm2 > 0.);
    double dt = deltaq_norm2 / mu;
    
    // dHdp and dq should be colinear, use this as a convergence criteria
    StateVec dHdp_opt = evalHamiltonianGradientWithP(qcenter, pstar);
    bool bc = areParallel(dHdp_opt, deltaq, tolerance_mu_min, maxPrintingAllowed);
    convergenceSanityCheck.add(bc);
    
    
    // add optimizing time
    //opt_deltaT.add(ev->t_opt);
    vec_dt.add(dt);
    
    // add optimizing momentum vector
    vec_pstar.add(pstar);
  
    // if success, keep track of gsl result as a starting point for next point in qcurve
    if (status == GSL_SUCCESS)
    {
      for (int k=0; k<n; k++)
        previous_gsl_result[k] = gsl_vector_get(s->x, k);
      gsl_status_previous_point = true;
    }
    else
    {
      gsl_status_previous_point = false;
    }
    /*
    if (maxPrintingAllowed)
    {
      cout << "GSL final status : " << gsl_strerror(status) << endl;
      
      cout << "residuals : ";
      for (int i=0; i<n; i++)
      {
        cout << gsl_vector_get(s->f, i) << " ";
      }
      cout << endl;
      
      
      cout << "J = " << endl;
      for (int i=0; i<n; i++)
      {
        for (int j=0; j<n; j++)
        {
          cout << gsl_matrix_get(s->J, i, j) << " ";
        }
        cout << endl;
      }
      
      cout << "solutions (ptild, s) : ";
      for (auto & el : ptild)
        cout << el << " ";
      cout << last << endl;
      
      
      cout << "gsl step descent norm : " << endl;
      cout << gsl_blas_dnrm2(s->dx);
      cout << endl << endl;
      //StateVec gsl_step;
      //for (int k=0; k<n; k++)
      //  gsl_step.add(gsl_vector_get(s->dx, k));
      //double gsl_step_nrm2 = norm2(gsl_step);
      //cout << "gsl descent step norm : " << gsl_step_nrm2 << endl;
      
    }
    */
    
    //gsl_multiroot_fsolver_free(s);
    gsl_multiroot_fdfsolver_free(s);
    gsl_vector_free(x);
    
  } // end loop over points in concentration curve
  
  // add a dummy element to gslStatus and collinear Status to make array match the number of points
  gslStatus.add(-999);
  convergenceSanityCheck.add(-999);
  residuals_H.add(-999.);
  StateVec dummy_residual_p;
  dummy_residual_p.insertMultiple(0, -999., simul->entities.size());
  residuals_p.add(dummy_residual_p);
  
  // returning results of the
  LiftTrajectoryOptResults output;
  output.opt_momentum = vec_pstar;
  output.opt_deltaT = vec_dt;
  output.gslStatus = gslStatus;
  output.collinearity = convergenceSanityCheck;
  output.residuals_H = residuals_H;
  output.residuals_p = residuals_p;
  
  return output;
  
}

/*
 // Npoints and nPoints - 1 non linear problem solved --> add a dummy final element
 gslStatus.add(-999);
 convergenceSanityCheck.add(-999);
 residuals_H.add(-999.);
 StateVec dummy_residual_p;
 dummy_residual_p.insertMultiple(0, -999., simul->entities.size());
 residuals_p.add(dummy_residual_p);
 
 
 // returning results of the
 LiftTrajectoryOptResults output;
 output.opt_momentum = vec_pstar;
 output.opt_deltaT = vec_dt;
 output.gslStatus = gslStatus;
 output.collinearity = convergenceSanityCheck;
 output.residuals_H = residuals_H;
 output.residuals_p = residuals_p;
 */





// argument n : dimension of the non-linear equations to resolve = number of entities
LiftTrajectoryOptResults NEP::findOptimalMomentumAndTime(const Curve& qcurve, const int n, bool maxPrintingAllowed)
{
  Array<double> vec_dt; // vector of optimal time assigned between each q(i) and q(i+1)
  Array<StateVec> vec_pstar; // vector of optimal momenta assigned between each q(i) and q(i+1)
  
  // keep track if GSL converged or not for each point of the concentration curve.
  Array<int> gslStatus;
  Array<int> convergenceSanityCheck;
  
  // residuals
  juce::Array<double> residuals_H;
  juce::Array<juce::Array<double>> residuals_p;
  
  bool gsl_status_previous_point = false;
  vector<double> previous_gsl_result(n, 0.);
  // loop over points in concentration space
  // q : q0 -- p*_0 -- q1 -- p*_1 --  .. -- qi -- p*_i -- q(i+1) -- p*_(i+1) -- ...
  for (int point=0; point<nPoints-1; point++) // n - 1 iterations
  {
    //if (maxPrintingAllowed)
      //cout << "Point #" << point << endl;
    
    // calculate q, dq of current concentration curve
    StateVec q = qcurve.getUnchecked(point);
    StateVec qnext = qcurve.getUnchecked(point+1);
    jassert(q.size() == qnext.size());
    StateVec qcenter;
    Array<double> deltaq;
    for (int m=0; m<q.size(); m++)
    {
      deltaq.add(qnext.getUnchecked(m) - q.getUnchecked(m));
      qcenter.add( 0.5* (q.getUnchecked(m) + qnext.getUnchecked(m)));
    }
    
    // encaps useful variables to pass to GSL
    EncapsVarForGSL ev;
    ev.qcenter = qcenter;
    ev.deltaq = deltaq;
    ev.nep = this;
    ev.epsilon = 1.;
    
    // momentum normalization initialized to unity
    Array<double> pnorm;
    pnorm.insertMultiple(0, 1., n);
   // if (gsl_status_previous_point)
   // {
    //  for (int m=0; m<n-1; m++)
    //  {
    //    if (gsl_vector_get(x, m) != 0.)
    //      pnorm.setUnchecked(m, abs(gsl_vector_get(x, m)));
    //  }
    //}
    ev.pnorm = pnorm;
    
    // equation normalization
    Array<double> eqnorm;
    eqnorm.insertMultiple(0, 1., n);
    ev.equation_norm = eqnorm;
    
    // initial value for p
    // x = (p, s)
    gsl_vector* x = initialOptimalGuess(n, gsl_status_previous_point, previous_gsl_result, qcenter);
    
    StateVec pinit;
    for (int k=0; k<x->size; k++)
    {
      pinit.add(gsl_vector_get(x, k));
    }
    StateVec dHdp_init = evalHamiltonianGradientWithP(qcenter, pinit);
    double sp_init = 0.;
    for (int k=0; k<pinit.size(); k++)
    {
      sp_init += dHdp_init.getUnchecked(k) * deltaq.getUnchecked(k);
    }
    //cout << "dH/dp • dq at initial condition = " << sp_init << endl;
    
    
    // build orthogonal basis of space orthogonal to dq
    dsp::Matrix<double> B = buildOrthogonalBasis(deltaq);
    ev.B = B;
    
    // init the gsl function and its derivatives
    gsl_multiroot_function_fdf fdf; // using jacobian
    fdf.f = residual4GSL;
    fdf.df = residual4GSL_df;
    fdf.fdf = residual4GSL_fdf; // combines function to evaluate and the jacobian
    fdf.n = n;
    fdf.params = &ev;
    
    // init gsl solver withtout derivative
    const gsl_multiroot_fdfsolver_type * T = gsl_multiroot_fdfsolver_hybridj;
    gsl_multiroot_fdfsolver * s = gsl_multiroot_fdfsolver_alloc(T, n);
    gsl_multiroot_fdfsolver_set(s, &fdf, x);
    
    // actual solving
    bool useContinuation = true;
    int status = gslMultirootSolving(s, fdf, ev, useContinuation);
    
    /*
    if (status == GSL_SUCCESS)
    {
      cout << "gsl succeeded without renormalization" << endl;
    }
    else
    {
      cout << "gsl did not succeed" << endl;
    }
    */
    
    //printLiftingJacobian(s, ev, n);
        
    
    // if not successful, try again normalizing the momenta variable with current state of the solver
    if (status != GSL_SUCCESS)
    {
      
      
      if (maxPrintingAllowed)
      {
        LOG("Renormalizing momentum variables and equations for point " + to_string(point)  + " !!");
        
        //cout << "current state : ";
        //for (int i=0; i<n; i++)
        //  cout << gsl_vector_get(s->x, i) << " ";
        //cout << endl;
        
        //cout << "residual : ";
        //for (int i=0; i<n; i++)
        //  cout << gsl_vector_get(s->f, i) << " ";
        //cout << endl;
        
        //printLiftingJacobian(s, ev, n);
      }
      
      // update momentum normalization with current values of p in gsl
      StateVec pprime;
      for (int m=0; m<n; m++)
      {
        double pm = gsl_vector_get(s->x, m);
        if (pm != 0.)
          ev.pnorm.setUnchecked(m, abs(pm));
        else
          ev.pnorm.setUnchecked(m, 1e-5);
        
        pprime.add(pm/ev.pnorm.getUnchecked(m));
        //gsl_vector_set(s->x, m, pm/ev.pnorm.getUnchecked(m));
        gsl_vector_set(s->x, m, 0.1);
      }
      //cout << "pnorm = ";
      //for (auto & pm : ev.pnorm)
      //  cout << pm << " ";
      //cout << endl;
      
      
      //printLiftingJacobian(s, ev, n);
      
      // to normalize equations
      StateVec equation_norm;
      
      // calculate jacobian in renormalized momentum
      StateVec dHdp = evalHamiltonianGradientWithP(qcenter, pprime);
      dsp::Matrix<double> hessian = evalHamiltonianHessianWithP(qcenter, pprime);
      dsp::Matrix<double> jaco = calculateLiftingJacobian(dHdp, hessian, ev.B, ev.pnorm,  ev.equation_norm, n);

      
      // use jacobian median of vector elements (matrix line 'i') to normalize equation 'i'.
      equation_norm.clear();
      equation_norm.insertMultiple(0, 1., n);
      jassert(jaco.getNumRows() == n);
      jassert(jaco.getNumColumns() == n);
      for (int i=0; i<jaco.getNumRows(); i++)
      {
        StateVec line;
        for (int j=0; j<jaco.getNumColumns(); j++)
          line.add(abs(jaco(i,j)));
        
        
        double si = 0.;
        for (auto & el : line)
          si += el;
        double NN = (double) line.size();
        si /= NN;
        
        if (si==0.)
          si = 1e-5;
        equation_norm.setUnchecked(i, si);
      }
      
      //cout << "eq norm : ";
      //for (auto & e : equation_norm)
      //  cout << e << " ";
      //cout << endl;
      
      // pass equation normalization to encapsulating variable
      ev.equation_norm = equation_norm;
  
      
      // calling again the multiroot solver
      useContinuation = false;
      status = gslMultirootSolving(s, fdf, ev, useContinuation);
    }
     
    
    // keep track of gsl status for current point
    gslStatus.add(status);
  

    //std::cout << "p0 = " << gsl_vector_get(s->x, 0) << "\n";
    //std::cout << "p1 = " << gsl_vector_get(s->x, 1) << "\n";
    //std::cout << "dt = " << gsl_vector_get(s->x, 1) << "\n";
    //cout << "used " << iter << " iterations" << endl;
    
    // retrieve results in a non-GSL form
    StateVec pstar;
    StateVec ptild;
    for (int m=0; m<n; m++)
    {
      pstar.add(gsl_vector_get(s->x, m) * ev.pnorm.getUnchecked(m));
      ptild.add(gsl_vector_get(s->x, m));
    }
    
    // dHdp and dq should be colinear, use this as a convergence criteria
    StateVec dHdp_opt = evalHamiltonianGradientWithP(qcenter, pstar);
    bool bc = areParallel(dHdp_opt, deltaq, 1e-8, maxPrintingAllowed);
    convergenceSanityCheck.add(bc);
    
    // deduce dt
    double norm2_dHdp_opt = norm2(dHdp_opt);
    double dt = 1.;
    if (norm2_dHdp_opt>0.)
    {
      dt = scalarProduct(dHdp_opt, deltaq) / (norm2_dHdp_opt*norm2_dHdp_opt);
    }
    else
    {
      LOGWARNING("Cannot assign dt to current point. || dHdp || = 0. Setting to 1.");
    }
    
    // add optimizing time
    //opt_deltaT.add(ev->t_opt);
    vec_dt.add(dt);
    
    // add optimizing momentum vector
    vec_pstar.add(pstar);
    
    // equation H(p,q) = 0
    // residuals
    residuals_H.add(abs(evalHamiltonian(qcenter, pstar)));
    juce::Array<double> rp;
    for (int k=0; k<dHdp_opt.size(); k++)
    {
      double r = dHdp_opt.getUnchecked(k) - deltaq.getUnchecked(k) / dt;
      rp.add(abs(r));
    }
    residuals_p.add(rp);
  
    // if success, keep track of gsl result as a starting point for next point in qcurve
    if (status == GSL_SUCCESS)
    {
      for (int k=0; k<n; k++)
        previous_gsl_result[k] = gsl_vector_get(s->x, k);
      gsl_status_previous_point = true;
    }
    else
    {
      gsl_status_previous_point = false;
    }
    
    if (maxPrintingAllowed)
    {
      //cout << "GSL final status : " << gsl_strerror(status) << endl;
      //cout << "Collinear sanity check : " << bc << endl;
      
      string residuals;
      for (int i=0; i<n; i++)
      {
       // cout << gsl_vector_get(s->f, i) << " ";
        residuals += " " + to_string(gsl_vector_get(s->f, i));
      }
      //cout << endl;
      //LOG("residuals : " + residuals);
      
      //if (status != GSL_SUCCESS)
      //  printLiftingJacobian(s, ev, n);
      
      //cout << "solutions p : ";
      //for (auto & el : ptild)
      //  cout << el << " ";
      //cout << "dt = " << dt << endl;
      
      
      //cout << "gsl step descent norm : " << endl;
      //cout << gsl_blas_dnrm2(s->dx);
      //cout << endl << endl;
    }
    
    //gsl_multiroot_fsolver_free(s);
    gsl_multiroot_fdfsolver_free(s);
    gsl_vector_free(x);
    
  } // end loop over points in concentration curve
  
  
  // Npoints and nPoints - 1 non linear problem solved --> add a dummy final element
  gslStatus.add(-999);
  convergenceSanityCheck.add(-999);
  residuals_H.add(-999.);
  StateVec dummy_residual_p;
  dummy_residual_p.insertMultiple(0, -999., simul->entities.size());
  residuals_p.add(dummy_residual_p);
  
  
  // returning results of the
  LiftTrajectoryOptResults output;
  output.opt_momentum = vec_pstar;
  output.opt_deltaT = vec_dt;
  output.gslStatus = gslStatus;
  output.collinearity = convergenceSanityCheck;
  output.residuals_H = residuals_H;
  output.residuals_p = residuals_p;
  
  return output;
  
}

// argument n : dimension of the non-linear equations to resolve = number of entities
LiftTrajectoryOptResults NEP::findOptimalMomentumAndTime_opt(const Curve& qcurve, const int n, bool maxPrintingAllowed)
{
  Array<double> vec_dt; // vector of optimal time assigned between each q(i) and q(i+1)
  Array<StateVec> vec_pstar; // vector of optimal momenta assigned between each q(i) and q(i+1)
  
  // keep track if GSL converged or not for each point of the concentration curve.
  Array<int> gslStatus;
  Array<int> convergenceSanityCheck;
  
  // residuals
  juce::Array<double> residuals_H;
  juce::Array<juce::Array<double>> residuals_p;
  
  bool gsl_status_previous_point = false;
  vector<double> previous_gsl_result(n, 0.1);
  // loop over points in concentration space
  // q : q0 -- p*_0 -- q1 -- p*_1 --  .. -- qi -- p*_i -- q(i+1) -- p*_(i+1) -- ...
  for (int point=0; point<nPoints-1; point++) // n - 1 iterations
  {
    //if (maxPrintingAllowed)
     // cout << "Point #" << point << endl;
    
    // calculate q, dq of current concentration curve
    StateVec q = qcurve.getUnchecked(point);
    StateVec qnext = qcurve.getUnchecked(point+1);
    jassert(q.size() == qnext.size());
    StateVec qcenter;
    Array<double> deltaq;
    for (int m=0; m<q.size(); m++)
    {
      deltaq.add(qnext.getUnchecked(m) - q.getUnchecked(m));
      qcenter.add( 0.5* (q.getUnchecked(m) + qnext.getUnchecked(m)));
    }
    
    // encaps useful variables to pass to GSL
    EncapsVarForGSL ev;
    ev.qcenter = qcenter;
    ev.deltaq = deltaq;
    ev.nep = this;
    ev.epsilon = 1.;
    
    // momentum normalization initialized to unity
    Array<double> pnorm;
    pnorm.insertMultiple(0, 1., n);
    ev.pnorm = pnorm;
    
    // equation normalization, initialized to unity
    Array<double> eqnorm;
    eqnorm.insertMultiple(0, 1., n);
    ev.equation_norm = eqnorm;
        
    // initial value for p
    // x = (p, s)
    gsl_vector* p = initialOptimalGuess(n, gsl_status_previous_point, previous_gsl_result, qcenter);
    
    
    // init the gsl function and its derivatives for non-linear problem in p
    gsl_multiroot_function_fdf fdf; // using jacobian
    fdf.f = residual4GSL_opt;
    fdf.df = residual4GSL_df_opt;
    fdf.fdf = residual4GSL_fdf_opt; // combines function to evaluate and the jacobian
    fdf.n = n;
    fdf.params = &ev;
    
    // init gsl solver with derivative
    const gsl_multiroot_fdfsolver_type * T_p = gsl_multiroot_fdfsolver_hybridj;
    gsl_multiroot_fdfsolver * s_p = gsl_multiroot_fdfsolver_alloc(T_p, n);
    gsl_multiroot_fdfsolver_set(s_p, &fdf, p);
    
    
    // encaps useful variables to pass to GSL
    StateVec pinit;
    for (int k=0; k<p->size; k++)
      pinit.add(gsl_vector_get(p, k));
    
    EncapsVarForGSL_MU evmu;
    evmu.q = qcenter;
    evmu.p = pinit;
    evmu.dq = deltaq;
    evmu.dq_norm2 = norm2(deltaq);
    evmu.nep = this;
    
    // init the gsl function for problem in mu
    gsl_function_fdf fdf_mu; // using jacobian
    fdf_mu.f = residual4GSL_mu_opt;
    fdf_mu.df = residual4GSL_mu_df_opt;
    fdf_mu.fdf = residual4GSL_mu_fdf_opt; // combines function to evaluate and the jacobian
    fdf_mu.params = &evmu;
    
    
    // init gsl solver with derivative
    const gsl_root_fdfsolver_type * T_mu = gsl_root_fdfsolver_newton;
    gsl_root_fdfsolver * s_mu = gsl_root_fdfsolver_alloc(T_mu);
    gsl_root_fdfsolver_set(s_mu, &fdf_mu, 1.);
    
    
    // actual solving
    int status = gslMultirootSolving_opt(s_p, s_mu, fdf, fdf_mu, ev, evmu);
    
    
    // if not successful, try again normalizing the momenta variable with current state of the solver
    if (status != 0)
    {
      if (maxPrintingAllowed)
      {
        LOG("Renormalizing momentum variables and equations for point " + to_string(point)  + " !!");
        
        //cout << "current state : ";
        //for (int i=0; i<n; i++)
        //  cout << gsl_vector_get(s->x, i) << " ";
        //cout << endl;
        
        //cout << "residual : ";
        //for (int i=0; i<n; i++)
        //  cout << gsl_vector_get(s->f, i) << " ";
        //cout << endl;
        
        //printLiftingJacobian(s, ev, n);
      }
      
      // update momentum normalization with norm2 of jacobian columns
      StateVec pnorm;
      for (int j=0; j<s_p->J->size2; j++) // columns loop
      {
        StateVec pcol;
        for (int i=0; i<s_p->J->size1; i++) // lines loop
          pcol.add(gsl_matrix_get(s_p->J, i, j));
        
        double pj = norm2(pcol);
        if (pj>0.)
          pnorm.add(pj);
        else
          pnorm.add(1e-6);
      }
      ev.pnorm = pnorm;
      
      //cout << "pnorm = ";
      //for (auto & pm : ev.pnorm)
      //  cout << pm << " ";
      //cout << endl;
      
      
      
      // reset momentum to dummy value
      for (int i=0; i<s_p->x->size; i++)
        gsl_vector_set(s_p->x, i, 0.1);
      
    /*
      // to normalize equations
      StateVec equation_norm;
      
      // calculate jacobian in renormalized momentum
      StateVec dHdp = evalHamiltonianGradientWithP(qcenter, pprime);
      dsp::Matrix<double> hessian = evalHamiltonianHessianWithP(qcenter, pprime);
      dsp::Matrix<double> jaco = calculateLiftingJacobian(dHdp, hessian, ev.B, ev.pnorm,  ev.equation_norm, n);

      
      // use jacobian median of vector elements (matrix line 'i') to normalize equation 'i'.
      equation_norm.clear();
      equation_norm.insertMultiple(0, 1., n);
      jassert(jaco.getNumRows() == n);
      jassert(jaco.getNumColumns() == n);
      for (int i=0; i<jaco.getNumRows(); i++)
      {
        StateVec line;
        for (int j=0; j<jaco.getNumColumns(); j++)
          line.add(abs(jaco(i,j)));
        
        
        double si = 0.;
        for (auto & el : line)
          si += el;
        double NN = (double) line.size();
        si /= NN;
        
        if (si==0.)
          si = 1e-5;
        equation_norm.setUnchecked(i, si);
      }
      
      //cout << "eq norm : ";
      //for (auto & e : equation_norm)
      //  cout << e << " ";
      //cout << endl;
      
      // pass equation normalization to encapsulating variable
      ev.equation_norm = equation_norm;
  */
      
      // calling again the multiroot solver
      status = gslMultirootSolving_opt(s_p, s_mu, fdf, fdf_mu, ev, evmu);

    }
    
     
    
    // keep track of gsl status for current point
    gslStatus.add(status);
  

    //std::cout << "p0 = " << gsl_vector_get(s->x, 0) << "\n";
    //std::cout << "p1 = " << gsl_vector_get(s->x, 1) << "\n";
    //std::cout << "dt = " << gsl_vector_get(s->x, 1) << "\n";
    //cout << "used " << iter << " iterations" << endl;
    
    // retrieve results in a non-GSL form
    StateVec pstar;
    StateVec ptild;
    for (int m=0; m<n; m++)
    {
      pstar.add(gsl_vector_get(s_p->x, m) * ev.pnorm.getUnchecked(m));
      ptild.add(gsl_vector_get(s_p->x, m));
    }
    
    // dHdp and dq should be colinear, use this as a convergence criteria
    StateVec dHdp_opt = evalHamiltonianGradientWithP(qcenter, pstar);
    bool bc = areParallel(dHdp_opt, deltaq, 1e-8, maxPrintingAllowed);
    convergenceSanityCheck.add(bc);
    
    // deduce dt
    //double norm2_dHdp_opt = norm2(dHdp_opt);
    double mu = exp(s_mu->root);
    double dt = norm2(deltaq) / mu;
    jassert( !isnan(dt) && !isinf(dt));
    
    // add optimizing time
    //opt_deltaT.add(ev->t_opt);
    vec_dt.add(dt);
    
    // add optimizing momentum vector
    vec_pstar.add(pstar);
    
    // equation H(p,q) = 0
    // residuals
    residuals_H.add(abs(evalHamiltonian(qcenter, pstar)));
    juce::Array<double> rp;
    for (int k=0; k<dHdp_opt.size(); k++)
    {
      double r = dHdp_opt.getUnchecked(k) - mu * deltaq.getUnchecked(k) / norm2(deltaq);
      rp.add(abs(r));
    }
    residuals_p.add(rp);
  
    // if success, keep track of gsl result as a starting point for next point in qcurve
    if (status == GSL_SUCCESS)
    {
      for (int k=0; k<n; k++)
        previous_gsl_result[k] = gsl_vector_get(s_p->x, k);
      gsl_status_previous_point = true;
    }
    else
    {
      gsl_status_previous_point = false;
    }
    
    if (maxPrintingAllowed)
    {
      //cout << "GSL final status : " << gsl_strerror(status) << endl;
      //cout << "Collinear sanity check : " << bc << endl;
      
      string residuals;
      for (int i=0; i<n; i++)
      {
       // cout << gsl_vector_get(s->f, i) << " ";
        residuals += " " + to_string(gsl_vector_get(s_p->f, i));
      }
      //cout << endl;
      //LOG("residuals : " + residuals);
      
      //if (status != GSL_SUCCESS)
      //  printLiftingJacobian(s, ev, n);
      
      //cout << "solutions p : ";
      //for (auto & el : ptild)
      //  cout << el << " ";
      //cout << "dt = " << dt << endl;
      
      
      //cout << "gsl step descent norm : " << endl;
      //cout << gsl_blas_dnrm2(s->dx);
      //cout << endl << endl;
    }
    
    gsl_multiroot_fdfsolver_free(s_p);
    gsl_root_fdfsolver_free(s_mu);
    gsl_vector_free(p);
    
  } // end loop over points in concentration curve
  
  
  // Npoints and nPoints - 1 non linear problem solved --> add a dummy final element
  gslStatus.add(-999);
  convergenceSanityCheck.add(-999);
  residuals_H.add(-999.);
  StateVec dummy_residual_p;
  dummy_residual_p.insertMultiple(0, -999., simul->entities.size());
  residuals_p.add(dummy_residual_p);
  
  // returning results of the
  LiftTrajectoryOptResults output;
  output.opt_momentum = vec_pstar;
  output.opt_deltaT = vec_dt;
  output.gslStatus = gslStatus;
  output.collinearity = convergenceSanityCheck;
  output.residuals_H = residuals_H;
  output.residuals_p = residuals_p;
  
  return output;
  
}






// argument n : dimension of the non-linear equations to resolve = number of entities
LiftTrajectoryOptResults NEP::findOptimalMomentumAndTime_LF(const Curve& qcurve, const int n, bool maxPrintingAllowed)
{
  //if (maxPrintingAllowed)
    //cout << "--- findOptimalMomentumAndTime_LF() ---" << endl;
  Array<double> vec_dt; // vector of optimal time assigned between each q(i) and q(i+1)
  Array<StateVec> vec_pstar; // vector of optimal momenta assigned between each q(i) and q(i+1)
  
  // keep track if GSL converged or not for each point of the concentration curve.
  Array<int> gslStatus;
  Array<int> convergenceSanityCheck;
  
  // residuals
  juce::Array<double> residuals_H;
  juce::Array<juce::Array<double>> residuals_p;
  
  bool gsl_status_previous_point = false;
  vector<double> previous_gsl_result(n, 0.1);
  // loop over points in concentration space
  // q : q0 -- p*_0 -- q1 -- p*_1 --  .. -- qi -- p*_i -- q(i+1) -- p*_(i+1) -- ...
  for (int point=0; point<nPoints-1; point++) // n - 1 iterations
  {
    //if (maxPrintingAllowed)
      //cout << "Point #" << point << endl;
    
    // calculate q, dq of current concentration curve
    StateVec q = qcurve.getUnchecked(point);
    StateVec qnext = qcurve.getUnchecked(point+1);
    jassert(q.size() == qnext.size());
    StateVec qcenter;
    Array<double> deltaq;
    for (int m=0; m<q.size(); m++)
    {
      deltaq.add(qnext.getUnchecked(m) - q.getUnchecked(m));
      qcenter.add( 0.5* (q.getUnchecked(m) + qnext.getUnchecked(m)));
    }
    
    //cout << "qcenter =" << endl;
    //for (auto & qi : qcenter)
    //  cout << " " << qi;
    //cout << endl;
      
    
    // encaps useful variables to pass to GSL
    EncapsVarForGSL ev;
    ev.qcenter = qcenter;
    ev.deltaq = deltaq;
    ev.nep = this;
    ev.epsilon = 1.;
    
    // momentum normalization initialized to unity
    Array<double> pnorm;
    pnorm.insertMultiple(0, 1., n);
    ev.pnorm = pnorm;
        
    // initial value for p
    // x = (p, s)
    gsl_vector* p = initialOptimalGuess(n, gsl_status_previous_point, previous_gsl_result, qcenter);
    
    
    // init the gsl function and its derivatives for non-linear problem in p
    gsl_multimin_function_fdf fdf; // using jacobian
    fdf.f = residual4GSL_LF;
    fdf.df = residual4GSL_df_LF;
    fdf.fdf = residual4GSL_fdf_LF; // combines function to evaluate and the jacobian
    fdf.n = n;
    fdf.params = &ev;
    
    
    // init gsl minimizer with derivative
    //const gsl_multimin_fdfminimizer_type * T = gsl_multimin_fdfminimizer_conjugate_fr; //gsl_multimin_fdfminimizer_vector_bfgs2;
    const gsl_multimin_fdfminimizer_type * T = gsl_multimin_fdfminimizer_vector_bfgs2; //gsl_multimin_fdfminimizer_vector_bfgs2;
    gsl_multimin_fdfminimizer * s_p = gsl_multimin_fdfminimizer_alloc (T, n);
    gsl_multimin_fdfminimizer_set(s_p, &fdf, p, 1., 1e-3);
    
    
    // encaps useful variables to pass to GSL
    StateVec pinit;
    for (int k=0; k<p->size; k++)
      pinit.add(gsl_vector_get(p, k));
    
    
    EncapsVarForGSL_MU evmu;
    evmu.q = qcenter;
    evmu.p = pinit;
    evmu.dq = deltaq;
    evmu.dq_norm2 = norm2(deltaq);
    evmu.nep = this;
    
    // init the gsl function for problem in mu
    gsl_function_fdf fdf_mu; // using jacobian
    fdf_mu.f = residual4GSL_mu_opt;
    fdf_mu.df = residual4GSL_mu_df_opt;
    fdf_mu.fdf = residual4GSL_mu_fdf_opt; // combines function to evaluate and the jacobian
    fdf_mu.params = &evmu;
    
    // init gsl solver with derivative
    const gsl_root_fdfsolver_type * T_mu = gsl_root_fdfsolver_steffenson; //gsl_root_fdfsolver_newton;
    gsl_root_fdfsolver * s_mu = gsl_root_fdfsolver_alloc(T_mu);
    gsl_root_fdfsolver_set(s_mu, &fdf_mu, 1.);
    
    
    // actual solving
    int status = gslMultirootSolving_LF(s_p, s_mu, fdf, fdf_mu, ev, evmu);
    
    // keep track of gsl status for current point
    gslStatus.add(status);
  

    //std::cout << "p0 = " << gsl_vector_get(s->x, 0) << "\n";
    //std::cout << "p1 = " << gsl_vector_get(s->x, 1) << "\n";
    //std::cout << "dt = " << gsl_vector_get(s->x, 1) << "\n";
    //cout << "used " << iter << " iterations" << endl;
    
    // retrieve results in a non-GSL form
    StateVec pstar;
    StateVec ptild;
    for (int m=0; m<n; m++)
    {
      pstar.add(gsl_vector_get(s_p->x, m)); //* ev.pnorm.getUnchecked(m));
      ptild.add(gsl_vector_get(s_p->x, m));
    }
    
    // dHdp and dq should be colinear, use this as a convergence criteria
    StateVec dHdp_opt = evalHamiltonianGradientWithP(qcenter, pstar);
    bool bc = areParallel(dHdp_opt, deltaq, tolerance_mu, maxPrintingAllowed);
    convergenceSanityCheck.add(bc);
    
    // deduce dt from mu
    double mu = exp(s_mu->root);
    double dt = norm2(deltaq) / mu;
    jassert( !isnan(dt) && !isinf(dt));
  
    
    // add optimizing time
    //opt_deltaT.add(ev->t_opt);
    vec_dt.add(dt);
    
    // add optimizing momentum vector
    vec_pstar.add(pstar);
    
    // residuals
    residuals_H.add(abs(evalHamiltonian(qcenter, pstar)));
    juce::Array<double> rp;
    for (int k=0; k<dHdp_opt.size(); k++)
    {
      double r = dHdp_opt.getUnchecked(k) - mu * deltaq.getUnchecked(k) / norm2(deltaq);
      rp.add(abs(r));
    }
    residuals_p.add(rp);
  
    // if success, keep track of gsl result as a starting point for next point in qcurve
    if (status == 1)
    {
      for (int k=0; k<n; k++)
        previous_gsl_result[k] = gsl_vector_get(s_p->x, k);
      gsl_status_previous_point = true;
    }
    else
    {
      gsl_status_previous_point = false;
    }
    
    // equation dH/dp = mu v
    //s_p->
    
    if (maxPrintingAllowed)
    {
      //cout << "GSL final status : " << gsl_strerror(status) << endl;
      //cout << "Collinear sanity check : " << bc << endl;
      
      //string residuals;
      //for (int i=0; i<n; i++)
      //{
       // cout << gsl_vector_get(s->f, i) << " ";
      //  residuals += " " + to_string(gsl_vector_get(s_p->f, i));
      //}
      //cout << endl;
      //LOG("residuals : " + residuals);
      
      //if (status != GSL_SUCCESS)
      //  printLiftingJacobian(s, ev, n);
      
      //cout << "solutions p : ";
      //for (auto & el : ptild)
      //  cout << el << " ";
      //cout << "s = " << s_mu->root << ". mu = " << mu <<  ". dt = " << dt << endl;
      
      
      //cout << "gsl step descent norm : " << endl;
      //cout << gsl_blas_dnrm2(s->dx);
      //cout << endl << endl;
    }
    
    gsl_multimin_fdfminimizer_free(s_p);
    gsl_root_fdfsolver_free(s_mu);
    gsl_vector_free(p);
    
  } // end loop over points in concentration curve
  
  
  // Npoints and nPoints - 1 non linear problem solved --> add a dummy final element
  gslStatus.add(-999);
  convergenceSanityCheck.add(-999);
  residuals_H.add(-999.);
  StateVec dummy_residual_p;
  dummy_residual_p.insertMultiple(0, -999., simul->entities.size());
  residuals_p.add(dummy_residual_p);
  
  // returning results of the
  LiftTrajectoryOptResults output;
  output.opt_momentum = vec_pstar;
  output.opt_deltaT = vec_dt;
  output.gslStatus = gslStatus;
  output.collinearity = convergenceSanityCheck;
  output.residuals_H = residuals_H;
  output.residuals_p = residuals_p;
  
  return output;
  
}





LiftTrajectoryOptResults NEP::liftCurveToTrajectoryWithGSL(const Curve& qcurve, bool maxPrintingAllowed)
{
  
  
  
  //cout << "--- NEP::liftCurveToTrajectoryWithGSL() ---" << endl;
  //cout << "input qcurve size = " << qcurve.size() << endl;
  // dimension of the problem
  const int n = simul->entities.size() + 1; // number of entities + 1
  
  // GSL to find optimal momentum and dt associated to qcurve
  LiftTrajectoryOptResults liftResults;
  if (solverType->getValueDataAsEnum<int>() == 0)
    liftResults = findOptimalMomentumAndTime_brutforce(qcurve, n, maxPrintingAllowed);
  else if (solverType->getValueDataAsEnum<int>() == 1)
    liftResults = findOptimalMomentumAndTime_opt(qcurve, n-1, maxPrintingAllowed);
  else if (solverType->getValueDataAsEnum<int>() == 2)
    liftResults = findOptimalMomentumAndTime_LF(qcurve, n-1, maxPrintingAllowed);
  else
    liftResults = findOptimalMomentumAndTime_brutforce(qcurve, n, maxPrintingAllowed);
  
  // for debugging
  if (maxPrinting->boolValue() && maxPrintingAllowed)
  {
    debugfile << "-- lifting optima found --" << endl;
    debugfile << "p* = [ ";
    int p=0;
    for (auto & ppoint : liftResults.opt_momentum)
    {
      debugfile << "(";
      int c=0;
      for (auto & pm : ppoint)
      {
        string closebracket = (p == liftResults.opt_momentum.size()-1 ? ") " : "), ");
        string comma = ( c==ppoint.size()-1 ? closebracket : "," );
        debugfile << pm << comma;
        c++;
      }
      p++;
    }
  debugfile << " ]" << endl;
  debugfile << "dt = [ ";
  p=0;
  for (auto & tpoint : liftResults.opt_deltaT)
  {
    string comma = (p == liftResults.opt_deltaT.size()-1 ? "" : ", ");
    debugfile << tpoint << comma;
    p++;
  }
  debugfile << " ]" << endl;
  }
  

  // Build full trajectory in (q ; p) space from optima found previously
  //pcurve.clear();
  //times.clear();
  pCurve pcurve;
  Array<double> times;
  
  // init a null vector
  Array<double> nullP;
  for (int i=0; i<Simulation::getInstance()->entities.size(); i++)
    nullP.add(0.);

  // first elements are 0
  double sumtime = 0.;
  pcurve.add(nullP);
  times.add(sumtime);
  for (int k=1; k<nPoints; k++) // nPoints-1 iterations
  {
    if (k==0)
      continue;
        
    // handle time
    sumtime += liftResults.opt_deltaT.getUnchecked(k-1);
    times.add(sumtime);
    
    // handle momentum, mean between current and next p
    if (k==nPoints-1) // force last momentum vec to be 0
      pcurve.add(nullP);
    else
    {
      StateVec meanP;
      for (int m=0; m<liftResults.opt_momentum.getUnchecked(k).size(); m++)
      {
        double pm = 0.5*(liftResults.opt_momentum.getUnchecked(k-1).getUnchecked(m) + liftResults.opt_momentum.getUnchecked(k).getUnchecked(m));
        meanP.add(pm);
      }
      pcurve.add(meanP);
    }
  }

  jassert(pcurve.size() == qcurve.size());
  jassert(times.size() == qcurve.size());
  
  // for debugging
  if (maxPrinting->boolValue() && maxPrintingAllowed)
  {
    debugfile << "-- Built momentum curve --" << endl;
    debugfile << "p = [ ";
    int p=0;
    for (auto & ppoint : pcurve)
    {
      debugfile << "(";
      int c=0;
      for (auto & pm : ppoint)
      {
        string closebracket = (p == pcurve.size()-1 ? ") " : "), ");
        string comma = ( c==ppoint.size()-1 ? closebracket : "," );
        debugfile << pm << comma;
        c++;
      }
      p++;
    }
  debugfile << " ]" << endl;
  }
  
  // moving average on pcurve (execpt first and last point that must remain 0)
  int window = 3;
  Trajectory av_pcurve;
  for (int k=0; k<pcurve.size(); k++)
  {
    StateVec avp;
    // loop over dimensions
    for (int dim=0; dim<pcurve.getUnchecked(k).size(); dim++)
    {
      int w = min(min(window, k), pcurve.size()-1-k);
      double av = 0.;
      double c = 0.;
      for (int k2=k-w; k2<=k+w; k2++)
      {
        c++;
        av += pcurve.getUnchecked(k2).getUnchecked(dim);
      }
      av /= c;
      avp.add(av);
    }
    jassert(avp.size() == n-1);
    av_pcurve.add(avp);
  }
  
  jassert(av_pcurve.size() == pcurve.size());
  //cout << "average pcurve size : " << av_pcurve.size() << endl;
  
  // for debugging
  if (maxPrinting->boolValue() && maxPrintingAllowed)
  {
    debugfile << "-- Filtered momentum curve --" << endl;
    debugfile << "p_av = [ ";
    int p=0;
    for (auto & ppoint : av_pcurve)
    {
      debugfile << "(";
      int c=0;
      for (auto & pm : ppoint)
      {
        string closebracket = (p == av_pcurve.size()-1 ? ") " : "), ");
        string comma = ( c==ppoint.size()-1 ? closebracket : "," );
        debugfile << pm << comma;
        c++;
      }
      p++;
    }
  debugfile << " ]" << endl;
  }
  
  
  /*
  // update global variables or not
  if (updateGlobalVar)
  {
    g_pcurve = pcurve;
    g_times = times;
  }
  */
  
  // Return optimization results
  //LiftTrajectoryOptResults output;
  //output.opt_deltaT = vec_dt;
  //output.opt_momentum = vec_pstar;
  //output.pcurve = pcurve;
  //output.times = times;
  
  liftResults.pcurve = pcurve;
  liftResults.times = times;
  
  
  
  return liftResults;
  
}


void NEP::setTimeNormalizationFactor()
{
  //LOGWARNING("timescale always set to 1.");
  //timescale_factor = 1.;
  //return;
  
  double meanK = 0.;
  double nreac = 0.;
  // loop over reactions
  for (auto & reaction : simul->reactions)
  {
    nreac++;
    meanK += reaction->assocRate;
    
    if (reaction->isReversible)
    {
      nreac++;
      meanK += reaction->dissocRate;
    }
  }
  
  // loop over entities
  for (auto & ent : simul->entities)
  {
    // destruction
    nreac++;
    meanK += ent->destructionRate;
    
    // creation
    if (ent->creationRate > 0.)
    {
      nreac++;
      meanK += ent->creationRate;
    }
  }
  
  if (nreac > 0. && meanK > 0.)
  {
    meanK /= nreac;
    timescale_factor = 1. / meanK;
  }
  else
  {
    timescale_factor = 1.;
  }
}




void NEP::initConcentrationCurve()
{
  // read init and final curve points from enum parameters
  int sstI = sst_stable->intValue();
  int sstF = sst_saddle->intValue();
  
  // add guard if initial steady state is unstable or final steady state is stable
  if (!simul->steadyStatesList->arraySteadyStates.getUnchecked(sstI).isStable || simul->steadyStatesList->arraySteadyStates.getUnchecked(sstF).isStable)
  {
    SteadyState sI = simul->steadyStatesList->arraySteadyStates.getUnchecked(sstI);
    SteadyState sF = simul->steadyStatesList->arraySteadyStates.getUnchecked(sstF);
    LOG("Initial steady state stability : " + to_string(sI.isStable) + ". Coordonates : ");
    simul->steadyStatesList->printOneSteadyState(sI);
    LOG("Final steady state stability : " + to_string(sF.isStable) + ". Coordonates : ");
    simul->steadyStatesList->printOneSteadyState(sF);
    throw std::runtime_error("Initial steady state should be stable, and final steady state unstable. Cannot perform descent.");
  }
  
  StateVec qI, qF;
  qI.insertMultiple(0, 0., simul->entities.size());
  qF.insertMultiple(0, 0., simul->entities.size());
  for (auto & pairI : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstI).state)
  {
    qI.set(pairI.first->idSAT, pairI.second);
  }
  for (auto & pairF : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstF).state)
  {
    qF.set(pairF.first->idSAT, pairF.second);
  }
  /*
  cout << "qI : ";
  for (auto & qi : qI)
    cout << qi <<" ";
  cout << endl;
  for (auto & qf : qF)
    cout << qf << " ";
  cout << endl;
  */
  
  jassert(qI.size() == simul->entities.size());
  jassert(qF.size() == simul->entities.size());
  
  // init q curve
  g_qcurve.clear();
  double NN = (double) nPoints;
  jassert(nPoints>1);
  
  if (initialConditions->getValueKey() == "Deterministic trajectory")
  {
    // copy the entities and reactions from simulation instance
    OwnedArray<SimEntity> entities;
    OwnedArray<SimReaction> reactions;
    entities.clear();
    reactions.clear();
    
    // If has not been called yet, the copy will not work properly
    simul->affectSATIds();
    
    // fill entity array with copies of the ones present in the simulation instance
    for (auto & ent : simul->entities)
      entities.add(ent->clone().release());
    
    for (auto & ent : entities)
    {
      ent->entity = nullptr; // just make sure this copied SimEntity will not interfere with Entity object
      ent->concent.resize(1);
      ent->previousConcent.resize(1);
      ent->startConcent.resize(1);
      ent->deterministicConcent.resize(1);
    }
    
    for (auto & r : simul->reactions)
    {
      Array<SimEntity*> reactants;
      Array<SimEntity*> products;
      for (auto & e : r->reactants)
      {
        reactants.add(entities[e->idSAT]);
      }
      for (auto & e : r->products)
      {
        products.add(entities[e->idSAT]);
      }
      SimReaction * copyr = new SimReaction(reactants, products, r->assocRate ,  r->dissocRate,  r->energy);
      reactions.add(copyr);
    }
    
    jassert(entities.size() == simul->entities.size());
    jassert(reactions.size() == simul->reactions.size());
    
    // set first point of qcurve = qF (unstable state)
    g_qcurve.add(qF);
    
    // set initial concentration of entities to be very close from qF in the direction of qI
    Curve sl = {qI, qF};
    double L = curveLength(sl);
    jassert(L>0.);
    for (int i=0; i<qI.size(); i++)
    {
      double ui = qF.getUnchecked(i) + 0.01 * ( qI.getUnchecked(i)-qF.getUnchecked(i) ) / L;
      entities[i]->concent.setUnchecked(0, ui);
      //entities[i]->startConcent.setUnchecked(0, ui);
    }
    
    
    // deterministic dynamics of the system until a stationnary state is reached
    double distance = 1000.;
    double precision = 1e-5;
    double timeout = (double) simul->dt->floatValue() * 50000;
    double t = 0.;
    int count = 0;
    bool delay = true; // require the deterministic search to run a minimum amount of time
    // otherwise, too close from an unstable steady state, variation might be too small
    while (distance>precision || delay)
    {
      count++;
      t += (double) simul->dt->floatValue();
      if (t>100.) // free the boolean delay
        delay = false;
      if (t>timeout)
        break;
      // deterministic traj
      kinetics->SteppingReactionRates(reactions, simul->dt->floatValue(), 0, false);
      kinetics->SteppingInflowOutflowRates(entities, simul->dt->floatValue(), 0);
      
      // update concentration values of entities
      for (auto & ent : entities)
      {
        ent->refresh();
      }
      
      // add new value to global qcurve
      StateVec qi;
      for (int k=0; k<entities.size(); k++)
        qi.add(entities[k]->concent.getUnchecked(0));
      g_qcurve.add(qi);
      
      // calculate variation in last dt
      distance = 0.;
      for (auto & ent : entities)
      {
        double deltaC = ent->concent.getUnchecked(0)-ent->previousConcent.getUnchecked(0);
        distance += deltaC*deltaC;
      }
      distance = sqrt(distance);
    } // end while
    
    // find in which steady state the system ended
    int reachedSST = -1;
    double dmin = 10000.;
    count = 0;
    for (auto & sst : simul->steadyStatesList->arraySteadyStates)
    {
      double d = 0.;
      for (auto & p : sst.state)
      {
        int entID = p.first->idSAT;
        SimEntity * se = entities.getUnchecked(entID);
        double dc = se->concent.getUnchecked(0) - p.second;
        d += dc*dc;
      }
      d = sqrt(d);
  
      if (d<dmin)
      {
        dmin = d;
        reachedSST = count;
      }
      count++;
    }
    
    if (reachedSST != sstI)
    {
      LOGWARNING("System converged to steady state " + to_string(reachedSST) + " while steady state " + to_string(sstI) + " was specified.");
      throw std::runtime_error("Deterministic trajectory method failed to init. concentration trajectory. System did not converge to the correct steady state.");
    }
    
    // set last point of qcurve = qI
    g_qcurve.add(qI);

    // reverse the direction of concentration curve
    std::reverse(g_qcurve.begin(), g_qcurve.end());
    
    // resample qcurve
    resampleInSpaceUniform(g_qcurve, nPoints);
  }
  else // use straightline
  {
    for (int point=0; point<nPoints; point++)
    {
      StateVec vec;
      double fpoint = (double) point;
      for (int k=0; k<qI.size(); k++)
      {
        double qk = qF.getUnchecked(k) + (1. - fpoint/(NN-1.)) * (qI.getUnchecked(k) - qF.getUnchecked(k));
        vec.add(qk);
      }
      g_qcurve.add(vec);
    }
  }
  
  // init sample rate
  length_qcurve = curveLength(g_qcurve);
  if (length_qcurve>0.)
    sampleRate = (double) nPoints / length_qcurve;
  else
  {
    LOGWARNING("qcurve has null length !!");
    sampleRate = 1000.;
  }
  /*
  // debugging
  cout << "curve size after init : " << g_qcurve.size() << ". nPoints = " << nPoints << endl;
  cout << "points are : " << endl;
  int c=-1;
  for (auto & q : g_qcurve)
  {
    c++;
    cout << "point #" << c << "   : ";
    for (auto & qi : q)
      cout << qi << " ";
    cout << endl;
  }
  */
  
}

void NEP::filterConcentrationTrajectory() // old
{
  //cout << "filtering concentration curve" << endl;
  // filter the gradient
  //filter.setCutoffFrequency(cutoffFreq->floatValue());
  //filter.prepare(sampleRate, simul->entities.size());
  //filter.setSamplingRate(sampleRate);
  //filter.setCutoffFrequency(cutoffFreq->floatValue());
  //filter.process(g_qcurve);
}


void NEP::updateDescentParams()
{
  //cout << "updating descent params" << endl;
  //cutoffFreq->setValue(cutoffFreq->floatValue() + 0.01);
  //nPoints += nPoints_increment;
  tolerance_mu /= 10.;
  
  std::ostringstream oss;
  oss << std::scientific << std::setprecision(4) << tolerance_mu;
  //LOG("tolerance on H(p,q)=0 residual is : " + oss.str());
}


bool NEP::descentShouldUpdateParams(double diffAction)
{
  //if ((diffAction<action_threshold->floatValue() || stepDescent<stepDescentThreshold))
  //{
    //bool b1 = diffAction<action_threshold->floatValue();
    //bool b2 = stepDescent<stepDescentThreshold;
    //cout << "Will update descent params. action criteria : " << b1;
    //cout << ". step descent criteria : " << b2 << endl;
  //}
  return ((diffAction<action_threshold->floatValue() || stepDescent<stepDescentThreshold));
}

bool NEP::descentShouldContinue(int step)
{
  //bool b = step<=Niterations->intValue();
  //bool b2 = cutoffFreq->floatValue()<maxcutoffFreq->floatValue();
  //return (step<=Niterations->intValue() && cutoffFreq->floatValue()<maxcutoffFreq->floatValue());
  return (step<=Niterations->intValue() && tolerance_mu > tolerance_mu_min);
}


void NEP::writeDescentToFile()
{
  // open output file
  system("mkdir -p descent");
  string filename = "descent/action-functionnal-descent_";
  filename += to_string(sst_stable->intValue()) + "->" + to_string(sst_saddle->intValue());
  filename += "_" + to_string(nPoints_max->intValue());
  filename += ".csv";
  ofstream historyFile;
  historyFile.open(filename, ofstream::out | ofstream::trunc);
  
  historyFile << "Descent characteristics used :" << endl;
  historyFile << "Number of iterations : " << Niterations->intValue() << endl;
  historyFile << "Initial condition : " << initialConditions->getValueKey() << endl;
  historyFile << "Action threshold : " << action_threshold->stringValue() << endl;
  historyFile << "Timescale factor : " << timescale_factor << endl;
  historyFile << "Initial step descent : " << stepDescentInitVal->floatValue() << endl;
  historyFile << "###############" << endl;
  
  historyFile << "iteration,point,gslStatus,collinearStatus,action";
  for (auto & ent : simul->entities)
    historyFile << ",q_" << ent->name;
  for (auto & ent : simul->entities)
    historyFile << ",p_" << ent->name;
  for (auto & ent : simul->entities)
    historyFile << ",dAdq_" << ent->name;
  //for (auto & ent : simul->entities)
  //  historyFile << ",dAdq_filt_" << ent->name;
  historyFile << ",res_H";
  for (auto & ent : simul->entities)
    historyFile << ",res_p_" << ent->name;
  historyFile << endl;
  
  //cout << "action descent size :" << actionDescent.size() << endl;
  //cout << "trajDescent descent size :" << trajDescent.size() << endl;
  //cout << "grad Descent size :" << dAdqDescent.size() << endl;
  //cout << "filtered grad Descent size :" << dAdqDescent_filt.size() << endl;
  jassert(actionDescent.size() == trajDescent.size());
  jassert(actionDescent.size() == dAdqDescent.size());
  //jassert(actionDescent.size() == dAdqDescent_filt.size());
  jassert(actionDescent.size() == gslStatus_descent.size());
  jassert(actionDescent.size() == collinearityStatus_descent.size());
  jassert(actionDescent.size() == residuals_H_descent.size());
  jassert(actionDescent.size() == residuals_p_descent.size());
  
  //cout << actionDescent.size() << " " << gslStatus_descent.size() << " " << collinearityStatus_descent.size() << " ";
  //cout << residuals_H_descent.size() << " " << residuals_p_descent.size() << endl;
  
  int nPoints_descent = actionDescent.size();
  
  for (int iter=0; iter<nPoints_descent; iter++) // loop over descent iterations
  {
    int npoint_local = trajDescent.getUnchecked(iter).size();
    for (int point=0; point<npoint_local; point++) // loop over curve points
    {
      historyFile << iter << "," << point;
      historyFile << "," << gslStatus_descent.getUnchecked(iter).getUnchecked(point) << "," << collinearityStatus_descent.getUnchecked(iter).getUnchecked(point);
      historyFile << "," << actionDescent.getUnchecked(iter).getUnchecked(point);
      
      PhaseSpaceVec trajpq = trajDescent.getUnchecked(iter).getUnchecked(point);
      StateVec dAdq_local = dAdqDescent.getUnchecked(iter).getUnchecked(point);
      //StateVec dAdq_filt_local = dAdqDescent_filt.getUnchecked(iter).getUnchecked(point);
      double resH = residuals_H_descent.getUnchecked(iter).getUnchecked(point);
      Array<double> resP = residuals_p_descent.getUnchecked(iter).getUnchecked(point);
      
      jassert(resP.size() == simul->entities.size());
      if (resP.size() != simul->entities.size())
        cout << resP.size() << " " << simul->entities.size() << endl;
      
      //cout << "trajectory size : " << trajpq.size() << endl;
      for (int m=0; m<trajpq.size()/2; m++)
        historyFile << "," << trajpq.getUnchecked(m);
      for (int m=trajpq.size()/2; m<trajpq.size(); m++)
        historyFile << "," << trajpq.getUnchecked(m);
      for (int m=0; m<dAdq_local.size(); m++)
        historyFile << "," << dAdq_local.getUnchecked(m);
      //for (int m=0; m<dAdq_filt_local.size(); m++)
      //  historyFile << "," << dAdq_filt_local.getUnchecked(m);
      historyFile << "," << std::scientific << residuals_H_descent.getUnchecked(iter).getUnchecked(point);
      for (int m=0; m<resP.size(); m++)
        historyFile << "," << resP.getUnchecked(m);
      historyFile << std::defaultfloat << endl;
    } // end loop over points in current iteration
    //historyFile << endl;
  } // end loop over iterations
  
}









// update concentration curve as q^I = q^(I-1) - stepDescent * dAdq_filtered
//void NEP::updateOptimalConcentrationCurve(Curve & _qcurve, double step)
bool NEP::updateOptimalConcentrationCurve(Curve & _qcurve, double step)
{
  Curve newqcurve = _qcurve;
  bool updateAllowed = true;

  for (int k=0; k<nPoints; k++)
  {
    // update curve point k component wise
    StateVec newqk;
    if (k==0 || k==nPoints-1)
    {
      newqk = newqcurve.getUnchecked(k);
    }
    else
    {
      for (int m=0; m<newqcurve.getUnchecked(k).size(); m++)
      {
        //newqk.add( _qcurve.getUnchecked(k).getUnchecked(m) - step * dAdq_filt.getUnchecked(k).getUnchecked(m) );
        double q = newqcurve.getUnchecked(k).getUnchecked(m) - step * dAdq.getUnchecked(k).getUnchecked(m);
        if (q<0. && updateAllowed)
          updateAllowed = false;
        newqk.add(q);
      }
    }
    newqcurve.setUnchecked(k, newqk);
    //qcurve.add(newqk);
  }
  //length_qcurve = curveLength(qcurve);
  //if (length_qcurve>0.)
  //  sampleRate = (double) nPoints / length_qcurve;
  jassert(_qcurve.size() == nPoints);
  
  // do not update concentration curve
  if (updateAllowed)
    _qcurve = newqcurve;
  
  return updateAllowed;
  
}



//double NEP::calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t)
Array<double> NEP::calculateAction(const Curve& qc, const Curve& pc, const Array<double>& t)
{
  //cout << "-- calculateAction() --" << endl;
  // check that pcurve, qcurve and tcurve have the same size
  jassert(qc.size() == pc.size());
  jassert(qc.size() == t.size());
  
  //cout << "--- calculate action along following curves ---" << endl;
  
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
    
  Array<double> hamilt;
  for (int i=0; i<qc.size(); i++)
  {
    hamilt.add(evalHamiltonian(qc.getUnchecked(i), pc.getUnchecked(i)));
    //cout << "H(" << i << ") = " << evalHamiltonian(qc.getUnchecked(i), pc.getUnchecked(i)) << endl;
  }
  
  // use trapezoidal rule to calculate action = integral(0, T, p•dq - H*dt)
  double newaction = 0.;
  Array<double> cumul_action;
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
    //cout << "p•dq = " << spdebug << "\tH_i "<< " = " << hamilt.getUnchecked(i) << endl;
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


//double NEP::backTrackingMethodForStepSize(const Curve& qc, const Curve& dAdq)
double NEP::backTrackingMethodForStepSize(const Curve& qc)
{
  // init step with previous value of stepDescent
  double step = stepDescentInit_dynamic;
  double minstep = 0.99*stepDescentThreshold;
  
  // time is such that minstep would be reached at last iteration
  int timeout = round(log(step/minstep) / log(2)) + 1;
  
  //cout << "NEP::backTrackingMethodForStepSize" << endl;
  //cout << "Init guess : " << step << endl;
  
  Array<double> cumulaction = calculateAction(qc, g_pcurve, g_times);
  double currentaction = cumulaction.getLast();
  /* debugging
  cout << "current action = " << currentaction << endl;
  cout << "current q = " ;
  for (auto & qm : qc.getUnchecked(nPoints/2))
    cout << qm << " ";
  cout << endl;
  cout << "deltaq = " ;
  for (auto & qm : deltaqc.getUnchecked(nPoints/2))
    cout << qm << " ";
  cout << endl;
  cout << "p = " ;
  for (auto & pm : g_pcurve.getUnchecked(nPoints/2))
    cout << pm << " ";
  cout << endl;
  cout << "t = " << g_times.getUnchecked(nPoints/2) << endl;
  */
  
  StateVec nullvec;
  nullvec.insertMultiple(0, 0., simul->entities.size());
  int count = 0;
 
  for (int iter=0; iter<timeout; iter++)
  {
    if (step<1e-5)
    {
      break;
    }
    count++;
    
    //cout << "trying step = " << step << endl;
    
    // update concentration curve corresponding to current step
    Curve newcurve = qc;
    bool updateIsValid = updateOptimalConcentrationCurve(newcurve, step);
    //cout << "update is Valid : " << updateIsValid << endl;
    
    if (!updateIsValid)
    {
      step *= 0.5;
      continue;
    }
    
    // find the corresponding lifted full trajectory, without updating global variables
    LiftTrajectoryOptResults liftResults = liftCurveToTrajectoryWithGSL(newcurve, false);
    
    /* debugging
    cout << "new q = ";
    for (auto & qm : newcurve.getUnchecked(nPoints/2))
      cout << qm << " ";
    cout << endl;
    cout << "new p = " ;
    for (auto & pm : g_pcurve.getUnchecked(nPoints/2))
      cout << pm << " ";
    cout << endl;
    cout << "new t = " << times.getUnchecked(nPoints/2) << endl;
    */
    
    /*
    // sanity check
    for (int point=0; point<nPoints; point++)
    {
      StateVec q = qc.getUnchecked(point);
      StateVec dq = deltaqc.getUnchecked(point);
      StateVec diff = newcurve.getUnchecked(point);
      cout << "step = " << step << endl;
      for (int m=0; m<q.size(); m++)
      {
        cout << q.getUnchecked(m) << " - " << dq.getUnchecked(m) << " = " << diff.getUnchecked(m) << endl;
      }
    }
    */
    
    // calculate action that would correspond to new concentration curve
    Array<double> newcumulaction = calculateAction(newcurve, liftResults.pcurve, liftResults.times);
    double newact = newcumulaction.getLast();
    //cout << "iter = " << iter << ". step = " << step << ". new action = " << newact << " vs current action = " << currentaction << endl;
    if (newact>=currentaction || newact<0.)
    {
      //cout << "decreasing step" << endl;
      step *= 0.5; // hardcoded (1/2)^17 = 7.6e-6, should be enough
      //cout << "new step val = " << step << endl;
    }
    else
    {
      //cout << "exiting loop" << endl;
      break;
    }
  }
  //cout << "used = " << count << " iterations in backtracking method" << endl;

  if (step<stepDescentThreshold)
  {
    step = 0.;
    stepDescentInit_dynamic *= 0.5;
  }
  if (step == stepDescentInitVal->floatValue())
  {
    stepDescentInit_dynamic *= 2.;
  }
  
  
  //LOGWARNING("backtracking algorithm did not converge to pick a descent step size. Returning 1e-6 as default value. Caution.");
  return step;
}


void NEP::applyButterworthFilter(juce::Array<double>& data, std::vector<juce::dsp::IIR::Filter<double>>& filters)
{
  for (int i = 0; i < data.size(); ++i)
  {
    double x = data[i];
    for (auto& f : filters)
      x = f.processSample(x);
    data.set(i, x);
  }
}

/*
//auto vector<juce::dsp::IIR::Filter<double>> makeFilters (coeffs)
vector<juce::dsp::IIR::Filter<double>> NEP::makeFilters(ReferenceCountedArray<IIRCoefficients> coeffs)
{
  vector<juce::dsp::IIR::Filter<double>> fs;
  for (auto& c : coeffs)
  {
    juce::dsp::IIR::Filter<double> f;
    for (size_t i=0; i<coeffs.size(); ++i)
        *chain.template get<i>().coefficients = *coeffs[i];
    //f.coefficients = c;
    fs.push_back(std::move(f));
  }
  return fs;
};

*/

// #HERE extremely slow, but seems to work though.
void NEP::resampleInSpaceUniform(Array<StateVec>& signal, int newsize)
{
  if (signal.size()<2 || newsize<2)
    return;
    
  /*
cout << "NEP::resampleInSpaceUniform()" << endl;
cout << "input = ";
for (int i=0; i<signal.size(); i++)
{
  for (int j=0; j<signal.getUnchecked(i).size(); j++)
  {
    string comma = (j==signal.getUnchecked(i).size()-1 ? "\n" : " , ");
    cout << signal.getUnchecked(i).getUnchecked(j) << comma;
  }
}
*/
    
  int dim = signal.getUnchecked(0).size();
  double d_newsize = (double) newsize;
  double L = curveLength(signal);
  
  // init newtraj with null vectors
  Trajectory resampled_signal;
  resampled_signal.resize(newsize);
  for (int i=0; i<newsize; ++i)
  {
    StateVec nullvec;
    nullvec.insertMultiple(0, 0., dim);
    resampled_signal.setUnchecked(i, nullvec);
  }
  
  // cumulative lengths of input signals
  Array<double> cumulative_lengths;
  cumulative_lengths.insertMultiple(0, 0., signal.size());
  for (int k=1; k<signal.size(); k++)
  {
    Trajectory segment({signal.getUnchecked(k-1), signal.getUnchecked(k)});
    cumulative_lengths.setUnchecked(k, cumulative_lengths.getUnchecked(k-1) + curveLength(segment));
  }
  
  //cout << "input signal length = " << L << endl;
 
  // resampling
  int last_closest = 0;
  for (int i=0; i<newsize; i++)
  {
    // linear distance between 0 and signal length
    double li = 0. + (double)i * L/(d_newsize-1.);
    
    //cout << "i = " << i << ". l_i = " << 100.*li/L << "%" << endl;
    
    // find closest matching index in cumulative length array
    auto it = lower_bound(cumulative_lengths.begin(), cumulative_lengths.end(), li);
    int closest = (int) distance(cumulative_lengths.begin(), it) - 1;
    closest = max(0, min(closest, (int)signal.size()-2)); // make sure closest is properly bounded
    
    // linear interpolation
    double l_inf = cumulative_lengths.getUnchecked(closest);
    double l_sup = cumulative_lengths.getUnchecked(closest+1);
    double alpha = (l_sup != l_inf) ? (li - l_inf) / (l_sup - l_inf) : 0.0;
    alpha = max(0., min(1., alpha));
    
    // keep track of current finding to accelerate next iteration
    last_closest = closest;
    
    //cout << "closest : " << closest << ". linf = " << 100.*l_inf/L << "% & lsup = " << 100*l_sup/L << "%" << endl;
    
    if (i==0)
    {
      resampled_signal.setUnchecked(i, signal.getFirst());
    }
    else if (i==newsize-1)
    {
      resampled_signal.setUnchecked(i, signal.getLast());
    }
    else
    {
      // interpolate between q[closest] and q[closest+1]
      for (int m=0; m<dim; m++)
      {
        double val = signal.getUnchecked(closest).getUnchecked(m) + alpha*(signal.getUnchecked(closest+1).getUnchecked(m)-signal.getUnchecked(closest).getUnchecked(m));
        resampled_signal.getReference(i).setUnchecked(m, val);
      } // end loop over dimension of the system
    } // end if
  }
  

  // modify input signal
  signal.resize(newsize);
  for (int i=0; i<newsize; i++)
  {
    signal.getReference(i).clear();
    signal.getReference(i).insertMultiple(0, 0., dim);
    for (int j=0; j<signal.getUnchecked(i).size(); j++)
    {
      signal.getReference(i).setUnchecked(j, resampled_signal.getUnchecked(i).getUnchecked(j));
    }
  }
  /*
  cout << "NEP::resampleInTimeUniform()" << endl;
  cout << "output = ";
  for (int i=0; i<signal.size(); i++)
  {
    for (int j=0; j<signal.getUnchecked(i).size(); j++)
    {
      string comma = (j==signal.getUnchecked(i).size()-1 ? "\n" : " , ");
      cout << signal.getUnchecked(i).getUnchecked(j) << comma;
    }
  }
  cout << endl;
  */
  
  
}


void NEP::resampleInTimeUniform(Array<StateVec>& signal, int size)
{
  if (signal.size()<2)
    return;
  
  if (signal.size() != g_times.size())
  {
    LOGWARNING("Cannot resample in time uniform, array sizes do not match.");
    return;
  }
    /*
  cout << "NEP::resampleInTimeUniform()" << endl;
  cout << "input = ";
  for (int i=0; i<signal.size(); i++)
  {
    for (int j=0; j<signal.getUnchecked(i).size(); j++)
    {
      string comma = (j==signal.getUnchecked(i).size()-1 ? "\n" : " , ");
      cout << signal.getUnchecked(i).getUnchecked(j) << comma;
    }
  }
  */
  
  //int N = signal.size();
  int dim = signal.getUnchecked(0).size();
  double dsize =  (double) size;
  double ti = g_times.getFirst();
  double tf = g_times.getLast();
  
  // init newtraj
  Trajectory resampled_signal;
  resampled_signal.resize(size);
  for (int i = 0; i<resampled_signal.size(); ++i)
    resampled_signal.getReference(i).resize(dim);
  
  /*
  cout << "tvec : ";
  for (auto & el : g_times)
    cout << el << " ";
  cout << endl;
  */
  
  for (int i=0; i<signal.size(); i++)
  {
    // linear timing between ti and tf
    double t = ti + (double)i * (tf-ti)/(dsize-1.);
    
    // find closest index in time
    int closest = 0;
    while (closest < signal.size()-1 && g_times.getUnchecked(closest+1)<t)
      closest++;
    
   // cout << "closest = " << closest << " & signal.size = " << signal.size() << endl;
    
    if (i==0)
    {
      resampled_signal.setUnchecked(i, signal.getFirst());
    }
    else if (i==signal.size()-1)
    {
      resampled_signal.setUnchecked(i, signal.getLast());
    }
    else
    {
      // interpolate between q[closest] and q[closest+1]
      double alpha = (t-g_times.getUnchecked(closest)) / (g_times.getUnchecked(closest+1)-g_times.getUnchecked(closest));
      for (int m=0; m<signal.getUnchecked(0).size(); m++)
      {
        double val = signal.getUnchecked(closest).getUnchecked(m) + alpha*(signal.getUnchecked(closest+1).getUnchecked(m)-signal.getUnchecked(closest).getUnchecked(m));
        resampled_signal.getReference(i).setUnchecked(m, val);
      } // end loop over dimension of the system
    } // end if
  }
  

  // modify input signal
  for (int i=0; i<signal.size(); i++)
  {
    for (int j=0; j<signal.getUnchecked(i).size(); j++)
      signal.getReference(i).setUnchecked(j, resampled_signal.getUnchecked(i).getUnchecked(j));
  }
  
  /*
  cout << "NEP::resampleInTimeUniform()" << endl;
  cout << "output = ";
  for (int i=0; i<signal.size(); i++)
  {
    for (int j=0; j<signal.getUnchecked(i).size(); j++)
    {
      string comma = (j==signal.getUnchecked(i).size()-1 ? "\n" : " , ");
      cout << signal.getUnchecked(i).getUnchecked(j) << comma;
    }
  }
  */
  
  
}
/*

void NEP::lowPassFiltering(Array<StateVec>& signal, bool isTimeUniform)
{
  if (signal.size() < 2 || g_times.size() < 2)
    return;
  
  int npoints = signal.size();
  int dim = signal.getFirst().size();
    
  // substract straight signal from input signal
  StateVec firstpoint = signal.getFirst();
  StateVec lastpoint = signal.getLast();
  /*
  //cout << "NEP::lowPassFiltering() 1st point : ";
  //for (auto & p : firstpoint)
  //  cout << p << " ";
  //cout << endl;
  //cout << "NEP::lowPassFiltering() last point : ";
  //for (auto & p : lastpoint)
  //  cout << p << " ";
  //cout << endl;
  
  
  if (isTimeUniform)
  {
    cout << "input time :{ " << endl;
    for (int i=0; i<g_times.size(); i++)
    {
      string comma = ( i==g_times.size()-1 ? "};" : "," );
      cout << g_times.getUnchecked(i) << comma;
    }
    cout << endl;
    
    cout << "input signal : " << endl;
    for (int i=0; i<signal.size(); i++)
    {
      cout << "signal.add({";
      for (int j=0; j<signal.getUnchecked(i).size(); j++)
      {
        string comma = ( j==signal.getUnchecked(i).size()-1? "});" : "," );
        cout << signal.getUnchecked(i).getUnchecked(j) << comma;
      }
      cout << endl;
    }
  }
  
  
  // build a modified signal which uses the firstpoint as origin and unitary vector u as direction
  // x'_i = xlast + ( 1 - i/(N-1) ) ( xfirst - xlast )
  Trajectory signal2;
  Trajectory straightline;
  for (int i=0; i<npoints; i++)
  {
    StateVec point;
    StateVec slpoint;
    double alpha = double(i) / double(npoints-1.);
    if (isTimeUniform)
    {
      double ttot = g_times.getLast() - g_times.getFirst();
      if (ttot>0)
        alpha = (g_times.getUnchecked(i)-g_times.getFirst()) / (g_times.getLast() - g_times.getFirst());
      else
      {
        LOGWARNING("Total time along trajectory is null, time filtering uses space uniform sampling");
        cout << "t = ";
        for (auto &t : g_times)
          cout << t << " ";
        cout << endl;
      }
    }
    for (int m=0; m<dim; m++)
    {
      //double pprime = lastpoint.getUnchecked(m) + (1. - double(i) / double(npoints-1.)) *
      //(firstpoint.getUnchecked(m)-lastpoint.getUnchecked(m))
      
      double pprime = firstpoint.getUnchecked(m) + alpha * (lastpoint.getUnchecked(m)-firstpoint.getUnchecked(m));
      point.add(signal.getUnchecked(i).getUnchecked(m)-pprime);
      slpoint.add(pprime);
    }
    signal2.add(point);
    straightline.add(slpoint);
  }
  
  //cout << "NEP::lowPassFilering() -- symmetrize" << endl;
  
  // (anti)symmetrise signal
  Trajectory signal_sym;
  int nprime = 2*npoints-1;
  for (int u=0; u<nprime; u++)
  {
    StateVec point;
    for (int m=0; m<dim; m++)
    {
      if (u<npoints-1)
        point.add(-1. * signal2.getUnchecked(npoints-u-1).getUnchecked(m));
      else
        point.add(signal2.getUnchecked(u-npoints+1).getUnchecked(m));
    }
    signal_sym.add(point);
  }
  
  //cout << "NEP::lowPassFilering() -- filter" << endl;
  
   
  // filtered trajectory init to be the symmetrized signal
  Trajectory signal2filter;
  for (auto & el : signal_sym)
    signal2filter.add(el);
  
  // actual filter
  
  // sampling rate set to 1 for filtering in space uniform
  float sr = 1.;
  if (isTimeUniform)
  {
    float timestep = g_times.getLast() / (float) (npoints-1.);
    if (timestep>0.)
      sr = 1./timestep;
    else
      LOGWARNING("time step is null --> sampling freq. = inf !! Use sampling rate of 1 by default, results should not be trusted.");
  }
  
  // interfaceUI gives max frequency in the signal. For instance 5 would mean any signal whose frequency is above 5 is suppressed.
  // this quantity is normalized to a sampling rate of 1.
  float juce_cutoffFreq = sr * cutoffFreq->floatValue();
  
  // if Nyquist condition is not met --> modify cutoff frequency, otherwise juce will complain
  if (juce_cutoffFreq >= sr/2.)
  {
    LOGWARNING("filtering above Nyquist frequency. Reducing cutoff freq. to Nyquist frequency.");
    juce_cutoffFreq = sr/2.;
    return;
  }

  // coeffs filtering
  auto coeffs = juce::dsp::FilterDesign<double>::designIIRLowpassHighOrderButterworthMethod(juce_cutoffFreq, sr, 4);
  
  // lambda function to get filters
  auto makeFilters = [&]()
  {
    std::vector<juce::dsp::IIR::Filter<double>> fs;
    for (auto& c : coeffs)
    {
      juce::dsp::IIR::Filter<double> f;
      f.coefficients = c;
      fs.push_back(std::move(f));
    }
    return fs;
  };
  
  
  for (int m=0; m<dim; m++)
  {
    Array<double> data;
    for (int i=0; i<signal2filter.size(); i++)
      data.add(signal2filter.getUnchecked(i).getUnchecked(m));
    
    // forward filter
    auto filters = makeFilters();
    applyButterworthFilter(data, filters);
    
    // reverse signal
    reverse(data.begin(), data.end());
    
    // backward filter
    filters = makeFilters();
    applyButterworthFilter(data, filters);
    
    // re-reverse signal
    std::reverse(data.begin(), data.end());
    
    //for (int i=0; i<data.size(); ++i)
   // {
   //   double x = data[i];
   //   for (auto& f : filters)
   //     x = f.processSample(x);
   //   data.set(i, x);
   // }
    
    
    // update original array
    for (int i=0; i<signal2filter.size(); i++)
      signal2filter.getReference(i).setUnchecked(m, data.getUnchecked(i));
      
  } // end loop over m
  
  // cout << "NEP::lowPassFilering() -- retrieve" << endl;
  
  // recover original signal filtered by taking only second half of symmetrized filtered signal
  for (int i=0; i<npoints; i++)
  {
    StateVec point;
    for (int m=0; m<dim; m++)
    {
      point.add( signal2filter.getUnchecked(i+npoints-1).getUnchecked(m) + straightline.getUnchecked(i).getUnchecked(m) );
      //point.add( straightline.getUnchecked(i).getUnchecked(m) );
    }
    if (i>0 && i<npoints-1) // do not modify first and last point of input signal
      signal.setUnchecked(i, point);
  }
  
  
} // end func


*/




// using Méthod of Leapfrog / Störmer–Verlet instead of Euler Method
void NEP::nextStepHamiltonEoM(StateVec& q, StateVec& p, double dt_in, const bool forward, bool& shouldStop, Trajectory & traj)
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


pair<Trajectory, Trajectory>  NEP::integrateHamiltonEquations(StateVec qi, StateVec pi)
{
 // dq/dt = dH/dp
 // dp/dt = -dH/dq
  double dt = 0.1;
  
  Trajectory traj_forward;
  Trajectory traj_backward;
  StateVec qcurrent_forward(qi);
  StateVec pcurrent_forward(pi);
  StateVec qcurrent_backward(qi);
  StateVec pcurrent_backward(pi);
  
  jassert(qi.size() == pi.size());
  bool break_forward = false;
  bool break_backward = false;
  
  //
  for (int st=0; st<1000; st++)
  {
    if (break_forward && break_backward)
      break;
    
    nextStepHamiltonEoM(qcurrent_forward, pcurrent_forward, dt, true, break_forward, traj_forward);
    nextStepHamiltonEoM(qcurrent_backward, pcurrent_backward, dt, false, break_backward, traj_backward);
    
  }
  
  pair<Trajectory, Trajectory> traj = make_pair(traj_forward, traj_backward); // one backward, one forward
  return traj;
  
  
}


void NEP::heteroclinicStudy()
{
  reset();

  // init concentration curve
  initConcentrationCurve();
  // lift it to full (q ; p) space
  //liftCurveToTrajectoryWithNLOPT_old();
  liftCurveToTrajectoryWithGSL(g_qcurve, true);
  /*
  // read stable and unstable fixed points
  int sstI = sst_stable->intValue();
  int sstF = sst_saddle->intValue();
  StateVec qI, qF;
  qI.insertMultiple(0, 0., simul->entities.size());
  qF.insertMultiple(0, 0., simul->entities.size());
  for (auto & pairI : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstI).state)
  {
    qI.set(pairI.first->idSAT, pairI.second);
  }
  for (auto & pairF : simul->steadyStatesList->arraySteadyStates.getUnchecked(sstF).state)
  {
    qF.set(pairF.first->idSAT, pairF.second);
  }
  */
  // define starting point for integrating hamilton equation of motion
  StateVec q_init;
  StateVec p_init;
  if (g_qcurve.size() > 1 && g_pcurve.size() > 1)
  {
    q_init = g_qcurve.getUnchecked(1);
    p_init = g_pcurve.getUnchecked(1);
  }
  else
  {
    LOG("Cannot perform heteroclinic study, concentration or momentum curves do not have enough points");
  }
  
  pair<Trajectory, Trajectory> trajs = integrateHamiltonEquations(q_init, p_init);
    
    // open output file
    String filename = "escape-paths_sst";
    filename += String(sst_stable->getValue().operator int()) + ".csv";
    ofstream historyFile;
    historyFile.open(filename.toStdString(), ofstream::out | ofstream::trunc);
    
    // first line
    historyFile << "point,forward";
    for (auto & ent : simul->entities)
      historyFile << ",q_" << ent->name;
    for (auto & ent : simul->entities)
      historyFile << ",p_" << ent->name;
    historyFile << endl;
    
    Trajectory trajfor = trajs.first;
    Trajectory trajback = trajs.second;
  
    // print forward trajectory
    for (int k=0; k<trajfor.size(); k++)
    {
      // print forward phase state vec ok iteration k
      historyFile << k << ",";
      historyFile << "1,";
      for (int m=0; m<trajfor.getUnchecked(k).size(); m++)
        historyFile << trajfor.getUnchecked(k).getUnchecked(m) << ",";
      historyFile << endl;
    }
    // print backward trajectory
    for (int k=0; k<trajback.size(); k++)
    {
      // print backward phase state vec ok iteration k
      historyFile << k << ",";
      historyFile << "0,";
      for (int m=0; m<trajback.getUnchecked(k).size(); m++)
        historyFile << trajback.getUnchecked(k).getUnchecked(m) << ",";
      historyFile << endl;
  }
  
}


void NEP::debuggingFunction()
{
  simul->affectSATIds();
  
  cout << "entity ordering:" << endl;
  int c=0;
  for (auto & ent : simul->entities)
  {
    cout << c << " --> " << ent->name << endl;
    c++;
  }
    
  //StateVec p = {-0.22216,-0.69937,-1.13313,-1.2904,-1.22887,-5.46028,-5.34574,-4.0164,-4.57388,-3.00375};
  StateVec pnull;
  pnull.insertMultiple(0, 0., 10);
  StateVec q = {0.55945, 0.55945, 2.22339, 9.08863, 0.13355, 0.19846, 0.19846, 2.22339, 9.08863, 0.13355};
  
  
  StateVec dHdq = evalHamiltonianGradientWithQ(q, pnull);
  StateVec dHdp = evalHamiltonianGradientWithP(q, pnull);
  
  cout << "dHdp = (";
  for (auto & el : dHdp)
    cout << " " << el;
  cout << ")" << endl;
  
  cout << "dHdq = (";
  for (auto & el : dHdq)
    cout << " " << el;
  cout << ")" << endl;
  
}


void NEP::loadJSONData(var data, bool createIfNotThere)
{
  updateSteadyStateList();
  // call mother class
  ControllableContainer::loadJSONData(data);
}
