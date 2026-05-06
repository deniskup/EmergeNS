//  NEPWorker.cpp
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//

#include "NEPWorker.h"



juce::dsp::Matrix<double> calculateLiftingJacobian_brutforce(EncapsVarForGSL& ev, StateVec p, double mu, const long int dim)
{
  juce::dsp::Matrix<double> jaco(dim, dim);
  
  StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(ev.q, p);
  juce::dsp::Matrix<double> hessian = ev.solver->evalHamiltonianHessianWithP(ev.q, p);
  
  
  assert(dHdp.size() == dim-1);
  assert(hessian.getSize().getUnchecked(0) == dim-1);
  assert(hessian.getSize().getUnchecked(1) == dim-1);
  assert(ev.dq.size() == dim-1);
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
          double norm2_dq = norm2(ev.dq);
          jassert(norm2_dq);
          jaco(i, j) = -1. * ev.epsilon * mu * ev.dq.getUnchecked(i-1) / (norm2_dq * ev.equation_norm.getUnchecked(i));
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




// dHdp must be properly normalized with respect to p when passed to this function
juce::dsp::Matrix<double> calculateLiftingJacobian(StateVec dHdp, juce::dsp::Matrix<double> hessian, juce::dsp::Matrix<double> B, StateVec pnorm, StateVec equation_norm, long int nvar)
{
  long int nrows = nvar;
  long int ncol = nvar;
  juce::dsp::Matrix<double> jaco(nrows, ncol);
  
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



void printLiftingJacobian_brutforce(gsl_multiroot_fdfsolver * s, EncapsVarForGSL ev, int n)
{
  StateVec p;
  for (int i=0; i<n-1; i++)
  {
    p.add(gsl_vector_get(s->x, i));
  }
  double mu = exp(gsl_vector_get(s->x, n-1));
  
  juce::dsp::Matrix<double> jaco = calculateLiftingJacobian_brutforce(ev, p, mu, n);
  
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
  
  StateVec q = ev.q;
  StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(q, p);
  juce::dsp::Matrix<double> hessian = ev.solver->evalHamiltonianHessianWithP(q, p);
  
  juce::dsp::Matrix<double> jaco = calculateLiftingJacobian(dHdp, hessian, ev.B, ev.pnorm, ev.equation_norm, n);
  
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




 
 //In the following the system to solve is :
 //H(p,q) = 0
 //epsilon * ( dH/dp - e^s * dq / || dq || ) = 0
 
// x size = number of entities in the system + 1
int residual4GSL_brutforce(const gsl_vector* x, void* params, gsl_vector* f)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->q.size() == 0 || ev->dq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = ev->q;
  StateVec dq = ev->dq;
  double norm2_dq = norm2(dq);
  assert(norm2_dq > 0.);
  juce::Array<double> pnorm = ev->pnorm;
  
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
  double H = ev->solver->evalHamiltonian(q, p);
  // calculate dH/dp
  StateVec dHdp = ev->solver->evalHamiltonianGradientWithP(q, p);
  
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
  if (ev->q.size() == 0 || ev->dq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = ev->q;
  StateVec dq = ev->dq;
  double norm2_dq = norm2(dq);
  assert(norm2_dq > 0.);
  juce::Array<double> pnorm = ev->pnorm;
  
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
  juce::dsp::Matrix<double> jaco = calculateLiftingJacobian_brutforce(*ev, p, mu, n);
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
  residual4GSL_brutforce(x, params, f);
  residual4GSL_df_brutforce(x, params, J);
  return GSL_SUCCESS;
}


int residual4GSL(const gsl_vector* x, void* params, gsl_vector* f)
{
  
  // retrieve q and dq
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->q.size() == 0 || ev->dq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  const unsigned long nvar = x->size;
  
  StateVec q = ev->q;
  juce::Array<double> pnorm = ev->pnorm;
  
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
  double H = ev->solver->evalHamiltonian(q, p);
  // calculate dH/dp
  StateVec dHdp = ev->solver->evalHamiltonianGradientWithP(q, p);
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
  if (ev->q.size() == 0 || ev->dq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  StateVec q = ev->q;
  
  juce::Array<double> pnorm = ev->pnorm;
  
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
  StateVec dHdp = ev->solver->evalHamiltonianGradientWithP(q, p);
  
  // calculate hessian
  juce::dsp::Matrix<double> hessian = ev->solver->evalHamiltonianHessianWithP(q, p);
  
  // set the jacobian elements associated to equations
  // H = 0
  // B • D-1 •  dH/dp = 0
  juce::dsp::Matrix<double> jaco = calculateLiftingJacobian(dHdp, hessian, ev->B, ev->pnorm, ev->equation_norm, nvar);
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
  residual4GSL(x, params, f);
  residual4GSL_df(x, params, J);
  return GSL_SUCCESS;
}


///////////////////////////////////////////

int residual4GSL_opt(const gsl_vector* x, void* params, gsl_vector* f)
{
  
  // retrieve encapsulated variables
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->q.size() == 0 || ev->dq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  const unsigned long nvar = x->size;
  
  // retrieve q, dq and pborm for more readability
  StateVec q = ev->q;
  StateVec dq = ev->dq;
  double dq_norm2 = norm2(dq);
  juce::Array<double> pnorm = ev->pnorm;
  
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
  StateVec dHdp = ev->solver->evalHamiltonianGradientWithP(q, p);
  jassert(dHdp.size() == nvar);

  // set the non-linear equalitites to solve by gsl
  for (int k=0; k<nvar ; k++)
  {
    jassert(pnorm.getUnchecked(k) > 0.);
    double uk = dHdp.getUnchecked(k) - mu * ev->dq.getUnchecked(k) / dq_norm2;
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
  if (ev->q.size() == 0 || ev->dq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return GSL_EINVAL;
  }
  const unsigned long nvar = x->size;
  
  // retrieve q, dq and pborm for more readability
  StateVec q = ev->q;
  StateVec dq = ev->dq;
  double dq_norm2 = norm2(dq);
  juce::Array<double> pnorm = ev->pnorm;
  
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
  juce::dsp::Matrix<double> hessian = ev->solver->evalHamiltonianHessianWithP(q, p);
  
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
  residual4GSL_opt(x, params, f);
  residual4GSL_df_opt(x, params, J);
  return GSL_SUCCESS;
  
}




double residual4GSL_mu_opt(double x, void* params)
{
  
  // retrieve encapsulated variables
  EncapsVarForGSL_MU * ev = static_cast<EncapsVarForGSL_MU*>(params);
    
  // calculate H
  double H = ev->solver->evalHamiltonian(ev->q, ev->p); // p depends on mu
  
  return H;

}


double residual4GSL_mu_df_opt(double x, void* params)
{
  
  // retrieve encapsulated variables
  EncapsVarForGSL_MU * ev = static_cast<EncapsVarForGSL_MU*>(params);
  
  double mu = exp(x);
  
  // calculate hessian
  juce::dsp::Matrix<double> hessian = ev->solver->evalHamiltonianHessianWithP(ev->q, ev->p);
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
  *y = residual4GSL_mu_opt(x, params);
  *dy = residual4GSL_mu_df_opt(x, params);
}



// using legendre fetchel inpired method
double residual4GSL_LF(const gsl_vector *x, void *params)
{
  
  // retrieve encapsulated variables
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->q.size() == 0 || ev->dq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return std::numeric_limits<double>::infinity();;
  }
  const unsigned long nvar = x->size;
  
  
  // retrieve q, dq and pborm for more readability
  StateVec q = ev->q;
  StateVec dq = ev->dq;
  double dq_norm2 = norm2(dq);
  juce::Array<double> pnorm = ev->pnorm;
  

  
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
  double H = ev->solver->evalHamiltonian(q, p);

  // set the non-linear equalitites to solve by gsl
  double sp = 0.;
  for (int k=0; k<nvar ; k++)
  {
    sp +=  ev->dq.getUnchecked(k) * p.getUnchecked(k);
  }
  sp *= mu / dq_norm2;
  
  
  return  (H - sp);
}


// x size = number of entities in the system
void residual4GSL_df_LF(const gsl_vector* x, void* params, gsl_vector *df)
{

  
  // retrieve encapsulated variables
  EncapsVarForGSL * ev = static_cast<EncapsVarForGSL*>(params);
  if (ev->q.size() == 0 || ev->dq.size() == 0)
  {
    LOGWARNING("null vector passed to GSL residual function, concentration curve not lifted properly to p-space.");
    return;
  }
  const unsigned long nvar = x->size;
  
  // retrieve q, dq and pborm for more readability
  StateVec q = ev->q;
  StateVec dq = ev->dq;
  double dq_norm2 = norm2(dq);
  juce::Array<double> pnorm = ev->pnorm;
  
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
  StateVec dHdp = ev->solver->evalHamiltonianGradientWithP(q, p);
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



NEPWorker::JobStatus NEPWorker::runJob()
{
  results = findOptimalMomentumAndTime();
  
  return jobHasFinished;
}




// Performs the actual multivariate solving.
// solve H(p, q) = 0 and epsilon * { dH(p,q)/dq - dp/dt } = 0 for increasing values of epsilon
// Arguments :
// s : the gsl multiroot solver used
// fdf : the multivariate gsl function for which gsl will attempt to find roots
// ev : home-made encapsulated variables to pass to gsl for the solving
// useContinutation : boolean to use continuation method for the solving
int NEPWorker::gslMultirootSolving_brutforce(gsl_multiroot_fdfsolver * s, gsl_multiroot_function_fdf & fdf, EncapsVarForGSL & ev, bool useContinuation)
{
  // continuation of the system
  double epsilon = 0.1;
  int status = GSL_CONTINUE;
  int iter = 0;
  
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
    
    while (status == GSL_CONTINUE && iter <= maxiteration)
    {
      iter++;
      //cout << "\titer" << iter << endl;
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
  
  
  int outstatus = (status == GSL_SUCCESS ? 1 : 0);

  return outstatus;
}






double NEPWorker::smoothUpdateOnMu(StateVec dHdp, StateVec dq, double dq_norm2)
{
  double mu = 1.;
  if (dq_norm2 <= 0.)
    return mu;

  mu = abs(scalarProduct(dHdp, dq));
  mu /= (dq_norm2*dq_norm2);
  
  return mu;
}








/*
int NEPWorker::solveForMomentumAtFixedMu_opt(gsl_multiroot_fdfsolver * s_p, EncapsVarForGSL& ev_p, double tolerance_p)
{
  int iter_p = 0;
  int gslstatus_p = GSL_CONTINUE;

  while (gslstatus_p == GSL_CONTINUE && iter_p <= maxiteration)
  {
    iter_p++;
    gslstatus_p = gsl_multiroot_fdfsolver_iterate(s_p);
    
    if (gslstatus_p != GSL_SUCCESS)
      break;
    
    //gslstatus_p = gsl_multimin_test_gradient(s_p->gradient, 1e-3);
    //gslstatus_p = test_convergence_colinear_method();
    
    // dHdp and dq should be colinear, use this as a convergence criteria
    StateVec currentP;
    currentP.insertMultiple(0, 0., (int) s_p->x->size);
    for (int k=0; k<s_p->x->size; k++)
      currentP.setUnchecked(k,  gsl_vector_get(s_p->x, k));
    StateVec dHdp_opt = ev_p.solver->evalHamiltonianGradientWithP(ev_p.q, currentP);
    bool bc = areParallel(dHdp_opt, ev_p.q, tolerance_p, false);
    
    if (bc)
      gslstatus_p = GSL_SUCCESS;
    else
      gslstatus_p = GSL_CONTINUE;
  }
  
  return gslstatus_p;
}
*/


/*
// Performs the actual multivariate solving. Arguments :
// s : the gsl multiroot solver used
// fdf : the multivariate vector function for which gsl will attempt to find roots
// ev : home-made encapsulated variables to pass to gsl for the solving
int NEPWorker::gslMultirootSolving_opt(gsl_multiroot_fdfsolver * s_p, gsl_root_fdfsolver* s_mu, gsl_multiroot_function_fdf & fdf_p, gsl_function_fdf& fdf_mu, EncapsVarForGSL & ev_p, EncapsVarForGSL_MU & ev_mu)
{
  // continuation of the system
  int iter_mu = 0;
  int iter_p = 0;
  //double tolerance = 1e-8;
  //double tolerance_mu = 1e-8;
  double residual_mu = 1000.;
  
  int gslstatus_p = GSL_CONTINUE;
  int gslstatus_mu = GSL_CONTINUE;
  
  // iteration on mu
  while (gslstatus_mu == GSL_CONTINUE && iter_mu <= maxiteration)
  {
    iter_mu++;
    gslstatus_p = GSL_CONTINUE;
    iter_p = 0;

    // set initial guess to output of previous iteration
    //gsl_vector * xprev = s_p->x;
    //gsl_multiroot_fdfsolver_set(s_p, &fdf, xprev);
    
    gslstatus_p = solveForMomentumAtFixedMu_opt(s_p, ev_p, tolerance);
    
    
    // retrieve current momentum
    StateVec currentP;
    currentP.insertMultiple(0, 0., (int)s_p->x->size);
    for (int k=0; k<s_p->x->size; k++)
      currentP.setUnchecked(k, gsl_vector_get(s_p->x, k));
    
    
    // pass its value to solver in mu
    ev_mu.p = currentP;
    fdf_mu.params = &ev_mu;
    gsl_root_fdfsolver_set(s_mu, &fdf_mu, s_mu->root);
    
    // update mu value with a single iteration
    if (residual4GSL_mu_df_opt(s_mu->root, &ev_mu) != 0.)
      gslstatus_mu = gsl_root_fdfsolver_iterate(s_mu);
    else // derivative might be 0, in this case use manual update on mu
    {
      // mu = dHdp • v / ||v||^2
      StateVec p;
      for (int k=0; k<s_p->x->size; k++)
        p.add(gsl_vector_get(s_p->x, k));
      StateVec dHdp = ev_p.solver->evalHamiltonianGradientWithP(ev_p.q, p);
      double mu = abs(scalarProduct(dHdp, ev_p.dq));
      if (ev.dq_norm2>0.)
        mu /= (ev.dq_norm2*ev.dq_norm2);
      s_mu->root = std::log(mu);
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
    gslstatus_mu = gsl_root_test_residual(residual_mu, tolerance);
    
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
  
  
  // should solve a final time for p !!

    
  int globalStatus = ( gslstatus_p == GSL_SUCCESS && gslstatus_mu == GSL_SUCCESS ? 1 : 0);


  return globalStatus;
}

*/









bool NEPWorker::solveForMomentumAtFixedMu_LF(gsl_multimin_fdfminimizer * s_p, EncapsVarForGSL& ev_p, double tolerance_p, int maxiter)
{
  int iter_p = 0;
  int gslstatus_p = GSL_CONTINUE;
  
  if (maxiter == -1)
    maxiter = maxiteration;
  
  bool converged = false;

  while (!converged && iter_p <= maxiter)
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
    StateVec dHdp_opt = ev_p.solver->evalHamiltonianGradientWithP(ev_p.q, currentP);
    bool bc = areParallel(dHdp_opt, ev_p.q, tolerance_p, false);
    
    if (bc)
      converged = true;
  }
  
  return converged;
}


// Performs the actual multivariate solving. Arguments :
// s : the gsl multiroot solver used
// fdf : the multivariate vector function for which gsl will attempt to find roots
// ev : home-made encapsulated variables to pass to gsl for the solving
int NEPWorker::gslMultirootSolving_LF(gsl_multimin_fdfminimizer * s_p, gsl_root_fdfsolver* s_mu, gsl_multimin_function_fdf & fdf_p, gsl_function_fdf& fdf_mu, EncapsVarForGSL & ev_p, EncapsVarForGSL_MU & ev_mu)
{
  
  //cout << "gslMultirootSolving_LF()" << endl;
  
  // continuation of the system
  int iter_mu = 0;

    
  //int gslstatus_p = GSL_CONTINUE;
  bool converged = false;
  bool converged_p = false;
  int gslstatus_mu = GSL_CONTINUE;
  
  StateVec p_initial;
  p_initial.insertMultiple(0, 0., (int) s_p->x->size);
  for (int k=0; k<s_p->x->size; k++)
    p_initial.setUnchecked(k, gsl_vector_get(s_p->x, k));

  double residual_mu = ev_p.solver->evalHamiltonian(ev_p.q, p_initial);
  
  // iteration on mu
  while (!converged && iter_mu <= maxiteration)
  {
    //cout << "iter_mu = " << iter_mu << endl;
    
    iter_mu++;
    //gslstatus_p = GSL_CONTINUE;
    
    // set initial guess to output of previous iteration
    //gsl_vector * xprev = s_p->x;
    //gsl_multiroot_fdfsolver_set(s_p, &fdf, xprev);
        
    // iteration on p, solve dH/dp = mu * dq / ||dq||
    
    int maxiter_p = maxiteration;
    if (abs(residual_mu) > 10000*tolerance)
      maxiter_p = 5;
    else if (abs(residual_mu) > 100*tolerance)
      maxiter_p = 10;
    converged_p = solveForMomentumAtFixedMu_LF(s_p, ev_p, tolerance, maxiter_p);
    
    // retrieve current momentum
    StateVec currentP;
    currentP.insertMultiple(0, 0., (int)s_p->x->size);
    for (int k=0; k<s_p->x->size; k++)
      currentP.setUnchecked(k, gsl_vector_get(s_p->x, k));
    
    // pass momentum value to solver in mu
    ev_mu.p = currentP;
    fdf_mu.params = &ev_mu;
    
    // residual in mu
    residual_mu = ev_p.solver->evalHamiltonian(ev_p.q, currentP);
    
    // global convergence status
    if (abs(residual_mu) < tolerance && converged_p)
    {
      converged = true;
      break;
    }
    
    
    // update on mu with a single iteration
    double mu_new;
    if (!converged_p) // smooth update on mu and proceed to next iteration
    {
      StateVec dHdp = ev_p.solver->evalHamiltonianGradientWithP(ev_p.q, currentP);
      mu_new = smoothUpdateOnMu(dHdp, ev_p.dq, ev_p.dq_norm2);
      s_mu->root = mu_new;
      //cout << "smooth update on mu as failed in p : " << mu << " and s = " << ev_p.s << endl;
      continue;
    }
    else
    {
      gslstatus_mu = gsl_root_fdfsolver_iterate(s_mu);
      mu_new = s_mu->root;
    }
    
    // check that mu_new value is valid
    if (isnan(mu_new) || isinf(mu_new) || mu_new<=0.)
    {
      gslstatus_mu = -1;
      break;
    }
    
    // safety guard
    mu_new = std::max(mu_new, 1e-12);
      
    // update mu in p solver
    ev_p.s = log(mu_new);
    
    // printing
    //StateVec v1 = evalHamiltonianGradientWithP(ev_p.qcenter, currentP);
    //StateVec v2 = ev_p.deltaq;
    //double sp = scalarProduct(v1, v2);
    //double ratio = sp / (norm2(v1)*norm2(v2));
    //double epsilon = 1. - ratio;
    //cout << "iter_p : " << iter_p << ". epsilon = " << epsilon << ". statusP : " << gsl_strerror(gslstatus_p) << endl;
  } // end while loop on mu
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
  //gslstatus_p = solveForMomentumAtFixedMu_LF(s_p, ev_p, tolerance_p);
    
  int globalStatus;
  if (converged)
    globalStatus = 1;
  else
  {
    if (gslstatus_mu == -1)
      globalStatus = -1;
    else
      globalStatus = 0;
  }

  return globalStatus;
}












// argument n : dimension of the non-linear equations to resolve
NLSresults NEPWorker::findOptimalMomentumAndTime()
{
  double dt = 1.; // optimal time assigned between each q(i) and q(i+1)
  StateVec pstar; // optimal momentum assigned between each q(i) and q(i+1)
  pstar.insertMultiple(0, 0., crn.entities.size());
  
  // keep track if GSL converged or not.
  int gslStatus = 0;
  int convergenceSanityCheck;
  
  // residuals
  double residuals_H;
  juce::Array<double> residuals_p;
  
  // nep solver to perform calculations
  ev.solver = solver;
    
  // init the gsl function and its derivatives
  gsl_multiroot_function_fdf fdf; // using jacobian
  fdf.params = &ev;
  gsl_multimin_function_fdf fdf_min;
  fdf_min.params = &ev;
  
  // Solve in p, s
  // H(p,q) = 0
  // dH/dp = exp(s) v with v = dq / ||dq|| and dt = ||dq|| exp(-s)
  if (nlsolverType == 0)
  {
    int n_local = ev.n;
    
    fdf.f = residual4GSL_brutforce;
    fdf.df = residual4GSL_df_brutforce;
    fdf.fdf = residual4GSL_fdf_brutforce; // combines function to evaluate and the jacobian
    fdf.n = n_local;
    
    // init x value
    gsl_vector* x = gsl_vector_alloc(n_local);
    for (int i=0; i<n_local; i++)
    {
      if (i<n_local-1)
        gsl_vector_set(x, i, ev.pstar_prev.getUnchecked(i));
      else
      {
        if (ev.dt_prev>0. && ev.dq_norm2>0.)
          gsl_vector_set(x, i, std::log(ev.dq_norm2/ev.dt_prev));
        else
          gsl_vector_set(x, i, 0.);
      }
    }
    
    // init gsl solver with derivative
    const gsl_multiroot_fdfsolver_type * T = gsl_multiroot_fdfsolver_hybridj;
    gsl_multiroot_fdfsolver * s = gsl_multiroot_fdfsolver_alloc(T, n_local);
    gsl_multiroot_fdfsolver_set(s, &fdf, x);
    
    // actual solving
    bool useContinuation = true;
    gslStatus = gslMultirootSolving_brutforce(s, fdf, ev, useContinuation);
    
    // retrieve results in a non-GSL form
    pstar.clear();
    for (int m=0; m<s->x->size-1; m++)
    {
      pstar.add(gsl_vector_get(s->x, m) * ev.pnorm.getUnchecked(m));
    }
    // dt
    double last = gsl_vector_get(s->x, n_local-1);
    double mu = exp(last);
    dt = ev.dq_norm2 / mu;
    if (isnan(dt) || isinf(dt) || dt==0.)
      gslStatus = -1;
    
    // keep track of residuals
    residuals_H = gsl_vector_get(s->f, 0);
    residuals_p.clear();
    for (int k=1; k<s->f->size; k++)
      residuals_p.add(gsl_vector_get(s->f, k));
    
    // free
    gsl_multiroot_fdfsolver_free(s);
    gsl_vector_free(x);
  }
  // solve separately
  // H(p,q) = 0
  // dH/dp = exp(s) v
  /*else if (nlsolverType == 1)
  {
    int n_local = ev.n - 1;
    
    fdf.f = residual4GSL_opt;
    fdf.df = residual4GSL_df_opt;
    fdf.fdf = residual4GSL_fdf_opt; // combines function to evaluate and the jacobian
    fdf.n = n_local;
    
    // init momentum value
    gsl_vector* p = gsl_vector_alloc(n_local);
    for (int i=0; i<n_local; i++)
    {
      gsl_vector_set(p, i, ev.pstar_prev.getUnchecked(i));
    }
    
    // init gsl solver with derivative
    const gsl_multiroot_fdfsolver_type * T_p = gsl_multiroot_fdfsolver_hybridj;
    gsl_multiroot_fdfsolver * s_p = gsl_multiroot_fdfsolver_alloc(T_p, n_local);
    gsl_multiroot_fdfsolver_set(s_p, &fdf, p);
    
    EncapsVarForGSL_MU evmu;
    evmu.q = ev.q;
    evmu.p = ev.pstar_prev;
    evmu.dq = ev.dq;
    evmu.dq_norm2 = ev.dq_norm2;
    evmu.solver = solver;
    
    // init the gsl function for problem in mu
    gsl_function_fdf fdf_mu; // using jacobian
    fdf_mu.f = residual4GSL_mu_opt;
    fdf_mu.df = residual4GSL_mu_df_opt;
    fdf_mu.fdf = residual4GSL_mu_fdf_opt; // combines function to evaluate and the jacobian
    fdf_mu.params = &evmu;
    
    
    // init gsl solver with derivative
    const gsl_root_fdfsolver_type * T_mu = gsl_root_fdfsolver_newton;
    gsl_root_fdfsolver * s_mu = gsl_root_fdfsolver_alloc(T_mu);
    gsl_root_fdfsolver_set(s_mu, &fdf_mu, ev.dt_prev);
    
    // actual solving
    gslStatus = gslMultirootSolving_opt(s_p, s_mu, fdf, fdf_mu, ev, evmu);
    
    // retrieve results in a non-GSL form
    pstar.clear();
    for (int m=0; m<n; m++)
    {
      pstar.add(gsl_vector_get(s_p->x, m) * ev.pnorm.getUnchecked(m));
    }
    // dt
    double mu = exp(s_mu->root);
    double dt = ev.dq_norm2 / mu;
    jassert(!isnan(dt) && !isinf(dt));
    if (isnan(dt) || isinf(dt) || dt==0.)
      gslStatus = -1;
    
    // residuals
    residuals_H.add(abs(evalHamiltonian(ev.q, pstar)));
    juce::Array<double> rp;
    for (int k=0; k<dHdp_opt.size(); k++)
    {
      double r = dHdp_opt.getUnchecked(k) - mu * ev.q.getUnchecked(k) / norm2(ev.q);
      rp.add(abs(r));
    }
    
    // free
    gsl_multiroot_fdfsolver_free(s_p);
    gsl_multiroot_fdfsolver_free(s_mu);
    gsl_vector_free(p);
  }*/
  else if (nlsolverType == 2)
  {
    int n_local = ev.n - 1;
    
    fdf_min.f = residual4GSL_LF;
    fdf_min.df = residual4GSL_df_LF;
    fdf_min.fdf = residual4GSL_fdf_LF; // combines function to evaluate and the jacobian
    fdf_min.n = n_local;
    
    // initial momentum value
    gsl_vector* p = gsl_vector_alloc(n_local);
    for (int i=0; i<n_local; i++)
      gsl_vector_set(p, i, ev.pstar_prev.getUnchecked(i));
    
    // init gsl minimizer with derivative
    //const gsl_multimin_fdfminimizer_type * T = gsl_multimin_fdfminimizer_conjugate_fr; //gsl_multimin_fdfminimizer_vector_bfgs2;
    const gsl_multimin_fdfminimizer_type * T = gsl_multimin_fdfminimizer_vector_bfgs2; //gsl_multimin_fdfminimizer_vector_bfgs2;
    gsl_multimin_fdfminimizer * s_p = gsl_multimin_fdfminimizer_alloc (T, n_local);
    gsl_multimin_fdfminimizer_set(s_p, &fdf_min, p, 1., tolerance);
    
    
    // encaps useful variables to pass to GSL
    StateVec pinit;
    for (int k=0; k<p->size; k++)
      pinit.add(gsl_vector_get(p, k));
    
    EncapsVarForGSL_MU evmu;
    evmu.q = ev.q;
    evmu.p = ev.pstar_prev;
    evmu.dq = ev.dq;
    evmu.dq_norm2 = ev.dq_norm2;
    evmu.solver = solver;
    
    // init the gsl function for problem in mu
    gsl_function_fdf fdf_mu; // using jacobian
    fdf_mu.f = residual4GSL_mu_opt;
    fdf_mu.df = residual4GSL_mu_df_opt;
    fdf_mu.fdf = residual4GSL_mu_fdf_opt; // combines function to evaluate and the jacobian
    fdf_mu.params = &evmu;
    
    // init gsl solver with derivative
    const gsl_root_fdfsolver_type * T_mu = gsl_root_fdfsolver_steffenson; //gsl_root_fdfsolver_newton;
    gsl_root_fdfsolver * s_mu = gsl_root_fdfsolver_alloc(T_mu);
    gsl_root_fdfsolver_set(s_mu, &fdf_mu, ev.dt_prev);
    
    // actual solving
    gslStatus = gslMultirootSolving_LF(s_p, s_mu, fdf_min, fdf_mu, ev, evmu);
  
    //std::cout << "p0 = " << gsl_vector_get(s->x, 0) << "\n";
    //std::cout << "p1 = " << gsl_vector_get(s->x, 1) << "\n";
    //std::cout << "dt = " << gsl_vector_get(s->x, 1) << "\n";
    //cout << "used " << iter << " iterations" << endl;
    
    // retrieve results in a non-GSL form
    pstar.clear();
    for (int m=0; m<s_p->x->size; m++)
    {
      pstar.add(gsl_vector_get(s_p->x, m)); //* ev.pnorm.getUnchecked(m));
    }
    // deduce dt from mu
    double mu = exp(s_mu->root);
    dt = ev.dq_norm2 / mu;
    jassert( !isnan(dt) && !isinf(dt));
    if (isnan(dt) || isinf(dt) || dt==0.)
      gslStatus = -1;
  
    // residuals
    // H(p,q) = 0
    residuals_H = abs(ev.solver->evalHamiltonian(ev.q, pstar));
    // dH/dp = mu • v
    juce::Array<double> rp;
    StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(ev.q, pstar);
    for (int k=0; k<dHdp.size(); k++)
    {
      double r = dHdp.getUnchecked(k) - mu * ev.dq.getUnchecked(k) / ev.dq_norm2;
      residuals_p.add(r);
    }
    
    // free
    gsl_multimin_fdfminimizer_free(s_p);
    gsl_root_fdfsolver_free(s_mu);
    gsl_vector_free(p);
  }
  else
  {
    LOGWARNING("Non-linear solver to use not properly selected.");
    gslStatus = -2;
  }
  
  // Handle case where residuals are above tolerance :
  // - renormalization & rescaling
  
    
  // dHdp and dq should be colinear, use this as a convergence criteria
  StateVec dHdp_opt = solver->evalHamiltonianGradientWithP(ev.q, pstar);
  convergenceSanityCheck = areParallel(dHdp_opt, ev.dq, tolerance, maxPrintingAllowed); 
  
 
  // returning results of the
  NLSresults output;
  output.dt = dt;
  output.pstar = pstar;
  output.gslStatus = gslStatus;
  output.collinearTest = convergenceSanityCheck;
  output.residual_H = residuals_H;
  output.residuals_p = residuals_p;
  
  return output;
  
}


// OLD STUFF

/*

// make sure to have dHdp parallel to dq, not anti-parallel.
// If antiparallel, apply p = p* + dp with dp = Hess-1 ( (v • dHdp) v - dHdp(p*) )
// and v = dq / ||dq||
// argument :
// gsl_vector s->x : current vector state within gsl solver
// EncapsVarForGSL& ev
void NEPWorker::correctMomentumDirectionIfFollowingWrongBranch(gsl_vector& x, StateVec q, StateVec dq)
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

*/

/*
// Performs the actual multivariate solving. Arguments :
// s : the gsl multiroot solver used
// fdf : the multivariate vector function for which gsl will attempt to find roots
// ev : home-made encapsulated variables to pass to gsl for the solving
int NEPWorker::gslMultirootSolving(gsl_multiroot_fdfsolver * s, gsl_multiroot_function_fdf & fdf, EncapsVarForGSL & ev, bool useContinuation)
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

*/
