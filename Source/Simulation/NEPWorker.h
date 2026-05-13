// 
//  NEPWorker.h
//  EmergeNS - App
//
//  Created by Thomas Kosc on 13/06/2025.
//  kosc.thomas@gmail.com
//


#pragma once

#include "JuceHeader.h"
#include "NEPSolver.h"
#include "NEPHelper.h"
//#include <nlopt.hpp>
#include <gsl/gsl_roots.h>
#include <gsl/gsl_multiroots.h>
#include <gsl/gsl_blas.h>
#include "gsl/gsl_multimin.h"

#include "IpoptConfig.h"
#include "IpIpoptApplication.hpp"
#include "IpTNLP.hpp"


#include <Eigen/Dense>

using namespace std;
using namespace Ipopt;


struct EncapsVarForNLOpt {
  const juce::Array<double>* q; // current concentration point
  const juce::Array<double>* dq;
  juce::Array<double>* p; // p variable to pass to t optimisation
  double t_opt; // t variable that optimizes the lagrangian
  //juce::Array<double> p_opt; // t variable that optimizes the lagrangian
};


struct EncapsVarForGSL {
  juce::Array<double> q; // current concentration point
  juce::Array<double> dq;
  double dq_norm2;
  double epsilon = 1.;
  juce::Array<double> pnorm;
  juce::Array<double> equation_norm;
  juce::dsp::Matrix<double> B{0, 0}; // elements lines are orthogonal basis of deltaq
  //double mu;
  double s;
  int n;
  StateVec pstar_prev;
  double dt_prev;
  NEPSolver * solver;
};


struct EncapsVarForGSL_MU {
  juce::Array<double> q; // current concentration point
  juce::Array<double> p;
  juce::Array<double> dq;
  double dq_norm2;
  NEPSolver * solver;
};


class IPOPTProblem : public TNLP
{
public:

  IPOPTProblem(const EncapsVarForGSL _ev, const int _idx): ev(_ev), idx(_idx){};


    virtual bool get_nlp_info(Index& n, Index& m, Index& nnz_jac_g, Index& nnz_h_lag, IndexStyleEnum& index_style)
    {
        n = ev.n; // number of variables (p, mu)
        m = 1; // number of constraints (H = 0)

        nnz_jac_g = n*m -1; // non-zeros entries of the jacobian ! n*m -1
        nnz_h_lag = 2; // Storage for the number of nonzero entries in the Hessian 

        index_style = TNLP::C_STYLE;
        return true;
    }

    virtual bool get_bounds_info(
        Index n,
        Number* x_l,
        Number* x_u,
        Index m,
        Number* g_l,
        Number* g_u)
    {
        for(int i=0;i<n;i++)
        {
            x_l[i] = -1e20;
            x_u[i] =  1e20;
        }

        // equality constraints
        for(int i=0;i<m;i++)
        {
            g_l[i] = 0.0;
            g_u[i] = 0.0;
        }

        return true;
    }

    virtual bool get_starting_point(
        Index n,
        bool init_x,
        Number* x,
        bool init_z,
        Number* z_L,
        Number* z_U,
        Index m,
        bool init_lambda,
        Number* lambda)
    {
        assert(init_x == true);

        x[0] = 1.0;
        x[1] = 1.0;
        x[2] = 1.0;

        return true;
    }

    // objective = 0
    virtual bool eval_f(Index n, const Number* x, bool new_x, Number& obj_value)
    {
        // extract p and mu from x
        StateVec sv_p;
        sv_p.insertMultiple(0, 0., n=1);
        for (int i=0;i<n-1;i++)
            sv_p.setUnchecked(i, x[i]);
        Number mu = x[n-1];

        // calculate hamiltonian
        double H = ev.solver->evalHamiltonian(sv_p, ev.q);

        // calcule scalar product p.v
        Number pv = scalarProduct(sv_p, ev.dq)/ev.dq_norm2;
   
        obj_value = H - mu*pv;
        return true;
    }

    virtual bool eval_grad_f(Index n, const Number* x, bool new_x, Number* grad_f)
    {
        // extract p and mu from x
        StateVec sv_p;
        sv_p.insertMultiple(0, 0., n=1);
        for (int i=0;i<n-1;i++)
            sv_p.setUnchecked(i, x[i]);
        Number mu = x[n-1];

        // calculate hamiltonian gradient with p
        StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(sv_p, ev.q);

        //f(p, mu) = H(p,q) - mu * p.v
        for (int k=0;k<n-2;k++)
        {
            grad_f[k] = dHdp.getUnchecked(k) - mu*ev.dq.getUnchecked(k)/ev.dq_norm2;
        }
        grad_f[n-1] = scalarProduct(sv_p, ev.dq)/ev.dq_norm2; 


        return true;
    }

    // constraints
    virtual bool eval_g(Index n, const Number* x, bool new_x, Index m, Number* g)
    {
        // extract p from x
        StateVec sv_p;
        sv_p.insertMultiple(0, 0., n=1);
        for (int i=0;i<n-1;i++)
            sv_p.setUnchecked(i, x[i]);

        Number h = ev.solver->evalHamiltonian(sv_p, ev.q);
        g[0] = h; // H(p,q) = 0

        return true;
    }

    // Jacobian of constraints
    virtual bool eval_jac_g(
        Index n,
        const Number* x,
        bool new_x,
        Index m,
        Index nele_jac,
        Index* iRow,
        Index *jCol,
        Number* values)
    {
        if (values == nullptr)
        {
            for (int j=0; j<n-1; j++)
            {
                iRow[j] = 0;   // just one constraint
                jCol[j] = j;   // derivative with respect to p_j
            }
            // mu derivative is zero, so we skip it in the jacobian
            return true;
        }
        else
        {
            // extract p and mu from x
            StateVec sv_p;
            sv_p.insertMultiple(0, 0., n=1);
            for (int i=0;i<n-1;i++)
                sv_p.setUnchecked(i, x[i]);
            Number mu = x[n-1];

            // calculate hamiltonian gradient w.r.t p
            StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(sv_p, ev.q);

            for (int j=0; j<n-1; j++)
            {
                values[j] = dHdp.getUnchecked(j); // dH/dp_j
            }

        }

        return true;
    }
/*
    // Hessian of Lagrangian
    virtual bool eval_h(
        Index n,
        const Number* x,
        bool new_x,
        Number obj_factor,
        Index m,
        const Number* lambda,
        bool new_lambda,
        Index nele_hess,
        Index* iRow,
        Index* jCol,
        Number* values)
    {
        if(values == nullptr)
        {
        }
        else
        {
        }

        return true;
    }
    */

    virtual void finalize_solution(
        SolverReturn status,
        Index n,
        const Number* x,
        const Number* z_L,
        const Number* z_U,
        Index m,
        const Number* g,
        const Number* lambda,
        Number obj_value,
        const IpoptData* ip_data,
        IpoptCalculatedQuantities* ip_cq)
    {
        std::cout << "\nSolution for point " << idx << ":\n";
        for (int i=0; i<n-1; i++)
        {
            std::cout << "p[" << i << "] = " << x[i] << "\n";
        }
        cout << "mu = " << x[n-1] << "\n";
    }

  private:
    EncapsVarForGSL ev;
    int idx;
}; // end class IPOPTProblem



class NEPWorker : public juce::ThreadPoolJob
{
public:
  NEPWorker(const CRNSnapshot & _crn, const EncapsVarForGSL _ev,  NLSresults & _results, double _tolerance, int _solverType, int _index, bool _maxPrintingAllowed)
  : juce::ThreadPoolJob("NEPWorker"), crn(_crn), ev(_ev), results(_results), tolerance(_tolerance), nlsolverType(_solverType), idx(_index), maxPrintingAllowed(_maxPrintingAllowed)
  {
    solver = new NEPSolver(crn);
  }

  
  JobStatus runJob() override;
  
private:
      
  void correctMomentumDirectionIfFollowingWrongBranch(gsl_vector&, StateVec, StateVec);
  
  int gslMultirootSolving_brutforce(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  
  //int gslMultirootSolving(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  
  double smoothUpdateOnMu(StateVec, StateVec, double);

  
  bool solveForMomentumAtFixedMu_opt(gsl_multiroot_fdfsolver *, EncapsVarForGSL&, double, int);
  int gslMultirootSolving_opt(gsl_multiroot_fdfsolver*, gsl_root_fdfsolver*, gsl_multiroot_function_fdf &, gsl_function_fdf&, EncapsVarForGSL &, EncapsVarForGSL_MU &);
  
  bool solveForMomentumAtFixedMu_LF(gsl_multimin_fdfminimizer *, EncapsVarForGSL&, double, int);
  int gslMultirootSolving_LF(gsl_multimin_fdfminimizer*, gsl_root_fdfsolver*, gsl_multimin_function_fdf &, gsl_function_fdf&, EncapsVarForGSL &, EncapsVarForGSL_MU &);
  
  
  NLSresults findOptimalMomentumAndTime();
  
  //LiftTrajectoryOptResults liftCurveToTrajectoryWithGSL(const Curve&, bool);
  
  NEPSolver * solver;
  
  const CRNSnapshot crn;
  
  EncapsVarForGSL ev;
  
  NLSresults & results;

  int idx;
  
  int nlsolverType;
  
  bool maxPrintingAllowed;
  
  double tolerance;
  
  int maxiteration = 100;
};

/*

{
public:
  NEP();

  NEP(juce::var data); // import from JSON
  ~NEP();

  juce::dsp::Matrix<double> buildOrthogonalBasis(StateVec v);
  
  gsl_vector * initialOptimalGuess_brutforce(const int, bool, const vector<double>, const StateVec);
  gsl_vector * initialOptimalGuess(const int, bool, const vector<double>, const StateVec);
  
  int gslMultirootSolving_brutforce(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  void correctMomentumDirectionIfFollowingWrongBranch(gsl_vector&, StateVec, StateVec);
  int gslMultirootSolving(gsl_multiroot_fdfsolver*, gsl_multiroot_function_fdf &, EncapsVarForGSL &, const bool useContinuation);
  int gslMultirootSolving_opt(gsl_multiroot_fdfsolver*, gsl_root_fdfsolver*, gsl_multiroot_function_fdf &, gsl_function_fdf&, EncapsVarForGSL &, EncapsVarForGSL_MU &);
  
  int solveForMomentumAtFixedMu(gsl_multimin_fdfminimizer *, EncapsVarForGSL&, double);
  int gslMultirootSolving_LF(gsl_multimin_fdfminimizer*, gsl_root_fdfsolver*, gsl_multimin_function_fdf &, gsl_function_fdf&, EncapsVarForGSL &, EncapsVarForGSL_MU &);
  
  LiftTrajectoryOptResults findOptimalMomentumAndTime_brutforce(const Curve&, const int n, bool);
  LiftTrajectoryOptResults findOptimalMomentumAndTime(const Curve&, const int n, bool);
  LiftTrajectoryOptResults findOptimalMomentumAndTime_opt(const Curve&, const int n, bool);
  LiftTrajectoryOptResults findOptimalMomentumAndTime_LF(const Curve&, const int n, bool);
    
  LiftTrajectoryOptResults liftCurveToTrajectoryWithGSL(const Curve&, bool);

  //LiftTrajectoryOptResults liftCurveToTrajectoryWithNLOPT_old();

   
};

*/
