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

#include <IpIpoptApplication.hpp>
#include "IpoptConfig.h"
#include "IpTNLP.hpp"

#include <Eigen/Dense>

using namespace std;
using namespace Ipopt;

static std::string ipoptStatusToString(Ipopt::ApplicationReturnStatus status)
{

    switch (status)
    {
        case Solve_Succeeded:
            return "Solve_Succeeded";

        case Solved_To_Acceptable_Level:
            return "Solved_To_Acceptable_Level";

        case Infeasible_Problem_Detected:
            return "Infeasible_Problem_Detected";

        case Search_Direction_Becomes_Too_Small:
            return "Search_Direction_Becomes_Too_Small";

        case Diverging_Iterates:
            return "Diverging_Iterates";

        case User_Requested_Stop:
            return "User_Requested_Stop";

        case Feasible_Point_Found:
            return "Feasible_Point_Found";

        case Maximum_Iterations_Exceeded:
            return "Maximum_Iterations_Exceeded";

        case Restoration_Failed:
            return "Restoration_Failed";

        case Error_In_Step_Computation:
            return "Error_In_Step_Computation";

        case Maximum_CpuTime_Exceeded:
            return "Maximum_CpuTime_Exceeded";

        case Not_Enough_Degrees_Of_Freedom:
            return "Not_Enough_Degrees_Of_Freedom";

        case Invalid_Problem_Definition:
            return "Invalid_Problem_Definition";

        case Invalid_Option:
            return "Invalid_Option";

        case Invalid_Number_Detected:
            return "Invalid_Number_Detected";

        case Unrecoverable_Exception:
            return "Unrecoverable_Exception";

        case NonIpopt_Exception_Thrown:
            return "NonIpopt_Exception_Thrown";

        case Insufficient_Memory:
            return "Insufficient_Memory";

        case Internal_Error:
            return "Internal_Error";

        default:
            return "Unknown_Status";
    }
}


class IPOPTProblem : public TNLP
{
public:

  //IPOPTProblem(const EncapsVarForGSL _ev, const int _idx): ev(_ev), idx(_idx){};
  IPOPTProblem(EncapsVarForGSL _ev, const int _idx, const bool _useChangeOfVariable): ev(_ev), idx(_idx), useChangeOfVariable(_useChangeOfVariable){};

  StateVec getPstar() const { return pstar; };
  double getS() const { return s; };
  double getMu() const { return mu; };


    virtual bool get_nlp_info(Index& n, Index& m, Index& nnz_jac_g, Index& nnz_h_lag, IndexStyleEnum& index_style)
    {
        n = ev.n; // number of variables (p, mu)
        m = 1; // number of constraints (H = 0)

        nnz_jac_g = n-1; // non-zeros entries of the constraint jacobian g(p,mu) = H(p)
        //nnz_h_lag = n*n - 1; // Storage for the number of nonzero entries in the Hessian 


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
            if (useChangeOfVariable) // use (u, mu) with u = exp(p) and mu = exp(s)
            {
                x_l[i] = 1e-20;
                x_u[i] = 1e20;
            }
            else // use (p,s) as variables with mu = exp(s)
            {
                x_l[i] = -1e20;
                x_u[i] =  1e20;
            }
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


        for (int k=0; k<n-1; k++)
        {
            if (useChangeOfVariable)
            {
                x[k] = std::exp(ev.pstar_prev.getUnchecked(k)); 
            }
            else
            {
                x[k] = ev.pstar_prev.getUnchecked(k);
            }
        }
        // init s0 value, mu0 = ||dq|| / dt = exp(s)
        double mu0 = 1.;
        if (ev.dt_prev>0. && ev.dq_norm2>0.)
            mu0 = std::log(ev.dq_norm2 / ev.dt_prev);

        if (useChangeOfVariable) // use mu as a variable
        {            
            x[n-1] = mu0;
        }
        else // use s = log(mu)
        {
            x[n-1] = std::log(mu0);
        }

        return true;
    }

    virtual bool eval_f(Index n, const Number* x, bool new_x, Number& obj_value)
    {
        // extract p/u and mu/s from x
        StateVec sv_pu;
        sv_pu.insertMultiple(0, 0., n-1);
        for (int i=0;i<n-1;i++)
            sv_pu.setUnchecked(i, x[i]);
        Number last = x[n-1];

        // check validity of extracted variables
        if (useChangeOfVariable)
        {
            for (auto& val : sv_pu)
            {
                if (val <= 0.)
                {
                    return false;
                }
            }
            if (last <= 0.)
                return false;
        }

        double value = 0.;
        if (useChangeOfVariable) // use (u, mu) as variables
        {
            // calculate hamiltonian gradient with u
            StateVec uxdHdu = ev.solver->evalUtimesHamiltonianGradientWithU(ev.q, sv_pu);

            for (int k=0; k<uxdHdu.size(); k++)
            {
                double valuek = uxdHdu.getUnchecked(k) - last * ev.v.getUnchecked(k);
                value += valuek * valuek;
            }

        }
        else
        {
            // calculate hamiltonian gradient with p
            StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(ev.q, sv_pu);

            // calcule scalar product p.v
            jassert(dHdp.size() == n-1);
            for (int k=0; k<dHdp.size(); k++)
            {
                double valuek = dHdp.getUnchecked(k) - std::exp(last) * ev.v.getUnchecked(k);
                value += valuek * valuek;
            }
        }

        value *= 0.5;

        obj_value = value;
        return true;
    }

    virtual bool eval_grad_f(Index n, const Number* x, bool new_x, Number* grad_f)
    {
        // extract p and mu from x
        StateVec sv_pu;
        sv_pu.insertMultiple(0, 0., n-1);
        for (int i=0;i<n-1;i++)
            sv_pu.setUnchecked(i, x[i]);
        Number mu;
        if (useChangeOfVariable)
            mu = x[n-1];
        else
             mu = std::exp(x[n-1]);

        // check validity of extracted variables
        if (useChangeOfVariable)
        {
            for (auto& val : sv_pu)
            {
                if (val <= 0.)
                    return false;
            }
            if (mu <= 0.)
                return false;
        }

        if (useChangeOfVariable)
        {
            // calculate hamiltonian gradient with u
            StateVec dHdu = ev.solver->evalHamiltonianGradientWithU(ev.q, sv_pu);

            // calculate hamiltonian hessian with u
            juce::dsp::Matrix<double> d2Hdu2 = ev.solver->evalHamiltonianHessianWithU(ev.q, sv_pu);

            jassert(d2Hdu2.getNumRows() == n-1);
            jassert(d2Hdu2.getNumColumns() == n-1);

            // build useful vector and matrix to calculate the gradient
            juce::dsp::Matrix<double> M(n-1, n-1);
            StateVec w;

            // Init them to 0
            M.clear();
            w.insertMultiple(0, 0., n-1);

            // fill them
            for (int i=0; i<n-1; i++)
            {
                for (int j=0; j<n-1; j++)
                {
                    M(i, j) = sv_pu.getUnchecked(j) * d2Hdu2(i, j) + (i==j ? dHdu.getUnchecked(i) : 0.);
                }
                w.setUnchecked(i, sv_pu.getUnchecked(i) * dHdu.getUnchecked(i) - mu * ev.v.getUnchecked(i));
            }

            // actual gradient calculation for first n-1 coordinates
            for (int i=0; i<n-1; i++)
            {
                double gradi = 0.;
                for (int j=0; j<n-1; j++)
                {
                    gradi += M(i, j) * w.getUnchecked(j);
                }
                grad_f[i] = gradi;
            }

            // last coordinates
            double grad_mu = 0.;
            for (int i=0; i<n-1; i++)
            {
                grad_mu += w.getUnchecked(i) * ev.v.getUnchecked(i);
            }
            grad_f[n-1] = -1. * grad_mu;

        }
        else
        {
            // calculate hamiltonian gradient with p
            StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(ev.q, sv_pu);

            // calculate hamiltonian hessain w.r.t p
            juce::dsp::Matrix<double> hess = ev.solver->evalHamiltonianHessianWithP(ev.q, sv_pu);

            // useful vector
            StateVec vectorToMultiply;
            vectorToMultiply.insertMultiple(0, 0., n-1);
            for (int k=0; k<n-1; k++)        
                vectorToMultiply.setUnchecked(k, dHdp.getUnchecked(k) - mu * ev.v.getUnchecked(k));
        

            //f(p, mu) = || dH(p,q)/dp - mu * v ||^2
            for (int i=0; i<n-1; i++)
            {
                double gradi = 0;
                for (int k=0; k<n-1; k++)
                {
                    gradi += hess(i, k) * vectorToMultiply.getUnchecked(k);
                }
                grad_f[i] = gradi;
            }

        
            grad_f[n-1] = -1. * scalarProduct(vectorToMultiply, ev.v) * mu; 
        }

        return true;
    }

    // constraints
    virtual bool eval_g(Index n, const Number* x, bool new_x, Index m, Number* g)
    {
        // extract pu from x
        StateVec sv_pu;
        sv_pu.insertMultiple(0, 0., n-1);
        for (int i=0;i<n-1;i++)
            sv_pu.setUnchecked(i, x[i]);

        // check validity of extracted variables
        if (useChangeOfVariable)
        {
            for (auto& val : sv_pu)
            {
                if (val <= 0.)
                    return false;
            }
        }

        Number h = ev.solver->evalHamiltonian(ev.q, sv_pu, useChangeOfVariable);
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
            return true;
        }
        else
        {
            // extract p and mu from x
            StateVec sv_pu;
            sv_pu.insertMultiple(0, 0., n-1);
            for (int i=0;i<n-1;i++)
                sv_pu.setUnchecked(i, x[i]);

            // check validity of extracted variables
            if (useChangeOfVariable)
            {
                for (auto& val : sv_pu)
                {
                    if (val <= 0.)
                        return false;
                }
            }

            if (useChangeOfVariable)
            {
                // calculate hamiltonian gradient w.r.t p
                StateVec dHdu = ev.solver->evalHamiltonianGradientWithU(ev.q, sv_pu);

                for (int j=0; j<n-1; j++)
                {
                    values[j] = dHdu.getUnchecked(j); // dH/du_j
                }
            }
            else
            {
                // calculate hamiltonian gradient w.r.t p
                StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(ev.q, sv_pu);

                for (int j=0; j<n-1; j++)
                {
                    values[j] = dHdp.getUnchecked(j); // dH/dp_j
                }
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
        //std::cout << "\nSolution for point " << idx << ":\n";
        pstar.clear();
        //std::cout << "p, mu = ";
        for (int i=0; i<n-1; i++)
        {
            //std::cout << " " << x[i];
            if (useChangeOfVariable)
            {
                if (x[i]>0.)
                    pstar.add(std::log(x[i]));
                else
                {
                    pstar.add(0.);
                    hasIssue = true;
                }
            }
            else
                pstar.add(x[i]);
        }

        if (useChangeOfVariable)
        {
            mu = x[n-1];
            if (mu>0.)
                s = std::log(mu);
            else
            {
                s = 0.;
                hasIssue = true;
            }
        }
        else
        {
            s = x[n-1];
            mu = std::exp(x[n-1]); 
        }
    }

  private:
    EncapsVarForGSL ev;
    int idx;
    StateVec pstar;
    double s;
    double mu;
    bool useChangeOfVariable = false;
    bool hasIssue = false;
}; // end class IPOPTProblem





/////////////////////////

class HamiltonProblem_falseMin : public TNLP
{
public:

  HamiltonProblem_falseMin(EncapsVarForGSL _ev, const int _idx): 
  ev(_ev), idx(_idx){};

  StateVec getPstar() const { return pstar; };
  double getS() const { return s; };
  double getMu() const { return mu; };

    virtual bool get_nlp_info(
        Index& n,
        Index& m,
        Index& nnz_jac_g,
        Index& nnz_h_lag,
        IndexStyleEnum& index_style)
    {
        n = ev.n; // number of variables (p, mu)
        m = ev.n; // number of constraints

        nnz_jac_g = n*n-1; // non-zeros entries of the constraint jacobian g(p,mu)
        //nnz_h_lag = n*n - 1; // Storage for the number of nonzero entries in the Hessian 


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

        for (int i=0;i<n-1;i++)
        {
            x[i] = ev.pstar_prev.getUnchecked(i);
        }

        double mu0 = 1.;
        if (ev.dt_prev>0. && ev.dq_norm2>0.)
            mu0 = std::log(ev.dq_norm2 / ev.dt_prev);
        x[n-1] = mu0;

        return true;
    }

    // objective = 0
    virtual bool eval_f(
        Index n,
        const Number* x,
        bool new_x,
        Number& obj_value)
    {
        obj_value = 0.0;
        return true;
    }

    virtual bool eval_grad_f(
        Index n,
        const Number* x,
        bool new_x,
        Number* grad_f)
    {
        for (int i=0; i<n; i++)
        {
            grad_f[i] = 0.0;
        }

        return true;
    }

    // constraints
    virtual bool eval_g(
        Index n,
        const Number* x,
        bool new_x,
        Index m,
        Number* g)
    {
        StateVec sv_p;
        sv_p.insertMultiple(0, 0., n-1);
        for (int i=0; i<n-1; i++)
            sv_p.setUnchecked(i, x[i]);
        double mu = std::exp(x[n-1]);

        // useful quantites
        double H = ev.solver->evalHamiltonian(ev.q, sv_p);
        StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(ev.q, sv_p);

        // dH/dp - mu v = 0
        for (int i=0; i<m-1; i++)
        {
            g[i] = dHdp.getUnchecked(i) - mu * ev.v.getUnchecked(i);
        }

        // H = 0
        g[m-1] = H;

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

        if (m != n)
        {
            cout << "Error in eval_jac_g : m should be equal to n" << endl;
            return false;
        }

        if(values == nullptr)
        {
            int idx = 0;
            for (int i=0; i<n; i++)
            {
                for (int j=0; j<n; j++)
                {
                    if (i == n-1 && j == n-1) // dH/dmu = 0
                        continue;
                    iRow[idx]=i; jCol[idx]=j; idx++;
                }
            }
        }
        else
        {
            StateVec sv_p;
            sv_p.insertMultiple(0, 0., n-1);
            for (int i=0; i<n-1; i++)
                sv_p.setUnchecked(i, x[i]);
            double mu = std::exp(x[n-1]);

            // useful quantites
            StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(ev.q, sv_p);
            juce::dsp::Matrix<double> hess = ev.solver->evalHamiltonianHessianWithP(ev.q, sv_p);

            int idx = 0;
            for (int i=0; i<n; i++)
            {
                for (int j=0; j<n; j++)
                {
                    if (i < n-1 && j < n-1) // d2H/dp2 
                    {
                        values[idx] = hess(i, j);
                    }
                    else if (i < n-1 &&j == n-1) // -v
                    {
                        values[idx] = -1. * ev.v.getUnchecked(i);
                    }
                    else if (i == n-1 && j < n-1) // (dH/dp)^T = 0
                    {
                        values[idx] = dHdp.getUnchecked(j);
                    }
                    idx++;
                }
            }
        }

        return true;
    }

    // Hessian of Lagrangian
    /*virtual bool eval_h(
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
            iRow[0]=0; jCol[0]=0;
            iRow[1]=1; jCol[1]=1;
        }
        else
        {
            // only constraint #2 contributes
            values[0] = lambda[2];
            values[1] = lambda[2];
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
        pstar.clear();
        for (int i=0; i<n-1; i++)
        {
            pstar.add(x[i]);
        }
        s = x[n-1];
        mu = std::exp(x[n-1]);
    }

private:
    EncapsVarForGSL ev;
    int idx;
    StateVec pstar;
    double s;
    double mu;
};




/////////////////////////

class HamiltonProblem_3 : public TNLP
{
public:

  HamiltonProblem_3(EncapsVarForGSL _ev, const int _idx): 
  ev(_ev), idx(_idx){};

  StateVec getPstar() const { return pstar; };
  //double getS() const { return s; };
  double getMu() const { return mu*dHdp_norm; };
  double getResidualH(){return residu_H;};
  juce::Array<double> getResidualP(){return residu_p;};

  void calculateResiduals()
  {
    // for equation H(p) = 0
    residu_H = abs(ev.solver->evalHamiltonian(ev.q, pstar)*dHdp_norm);

    // for equations dH/dp = mu v
    residu_p.clear();
    StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(ev.q, pstar);
    for (int k=0; k<dHdp.size(); k++)
    {
        double r = std::abs(dHdp.getUnchecked(k)- mu*ev.v.getUnchecked(k));
        r *= dHdp_norm;
        residu_p.add(r);
    }


  }

    virtual bool get_nlp_info(
        Index& n,
        Index& m,
        Index& nnz_jac_g,
        Index& nnz_h_lag,
        IndexStyleEnum& index_style)
    {
        int dim = ev.n - 1;

        n = dim; // number of variables (p)
        m = 1; // number of constraints

        nnz_jac_g = dim; // non-zeros entries of the constraint jacobian g(p,mu)
        nnz_h_lag = dim*dim; // Storage for the number of nonzero entries in the Hessian of the lagrangian

        // norm of dHdp
        StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(ev.q, ev.pstar_prev);
        //dHdp_norm = norm2(dHdp);
        if (dHdp_norm == 0.)
            dHdp_norm = 1.;
        ev.solver->setCRNNormalization(1. / dHdp_norm);



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

        for (int i=0;i<n;i++)
        {
            x[i] = ev.pstar_prev.getUnchecked(i);
        }

        return true;
    }

    // objective = 0
    virtual bool eval_f( // = -p.v
        Index n,
        const Number* x,
        bool new_x,
        Number& obj_value)
    {
        obj_value = 0.0;
        if (ev.v.size() != n)
        {
            return false;
        }
        for (int i=0; i<n; i++)
        {
        obj_value -= ev.v.getUnchecked(i) * x[i];
        }

        return true;
    }

    virtual bool eval_grad_f(
        Index n,
        const Number* x,
        bool new_x,
        Number* grad_f)
    {
        for (int i=0; i<n; i++)
        {
            grad_f[i] = -1. * ev.v.getUnchecked(i);
        }

        return true;
    }

    // constraints
    virtual bool eval_g(
        Index n,
        const Number* x,
        bool new_x,
        Index m,
        Number* g)
    {
        StateVec sv_p;
        sv_p.insertMultiple(0, 0., n);
        for (int i=0; i<n; i++)
            sv_p.setUnchecked(i, x[i]);
    

        // useful quantites
        double H = ev.solver->evalHamiltonian(ev.q, sv_p);

        g[0] = H;

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

        

        if(values == nullptr)
        {
            int idx = 0;
            for (int i=0; i<n; i++)
            {
                iRow[idx] = 0;   // just one constraint
                jCol[idx] = i;   // derivative with respect to p_i
                idx++;
            }
        }
        else
        {
            StateVec sv_p;
            sv_p.insertMultiple(0, 0., n);
            for (int i=0; i<n; i++)
                sv_p.setUnchecked(i, x[i]);

            // useful quantites
            StateVec dHdp = ev.solver->evalHamiltonianGradientWithP(ev.q, sv_p);

            if (dHdp.size() != n)
            {
                return false;
            }

            for (int i=0; i<n; i++)
            {
                values[i] = dHdp.getUnchecked(i); // dH/dp_i
            }
        }

        return true;
    }

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
            int idx = 0;
            for (int i=0; i<n; i++)
            {
                for (int j=0; j<n; j++)
                {
                    iRow[idx] = i;
                    jCol[idx] = j;
                    idx++;
                }
            }
        }
        else
        {

            // retrieve p
            StateVec sv_p;
            sv_p.insertMultiple(0, 0., n);
            for (int i=0; i<n; i++)
                sv_p.setUnchecked(i, x[i]);

            juce::dsp::Matrix<double> hess = ev.solver->evalHamiltonianHessianWithP(ev.q, sv_p);

            // hessian of the lagrangian = lambda * hessian of H
            int idx = 0;
            for (int i=0; i<n; i++)
            {
                for (int j=0; j<n; j++)
                {
                    values[idx] = lambda[0] * hess(i, j);
                    idx++;
                }
            }

        }

        return true;
    }
    

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
        pstar.clear();
        for (int i=0; i<n; i++)
        {
            pstar.add(x[i]);
        }
        if (lambda[0]<=0.)
        {
            //s = 0.;
            mu = 1.;
        }
        else
        {
            //s = std::log(lambda[0]);
            mu = 1. / lambda[0];
        }

        calculateResiduals();
    }

private:
    EncapsVarForGSL ev;
    int idx;
    StateVec pstar;
    //double s;
    double mu;
    double dHdp_norm = 1.;
    double residu_H = 0.;
    juce::Array<double> residu_p = 0.;
};









class NEPWorker : public juce::ThreadPoolJob
{
public:
  NEPWorker(CRNSnapshot _crn, const EncapsVarForGSL _ev,  NLSresults & _results, double _tolerance, int _solverType, int _index, bool _maxPrintingAllowed, bool _useChangeOfVariable)
  : juce::ThreadPoolJob("NEPWorker"), crn(_crn), ev(_ev), results(_results), tolerance(_tolerance), 
  nlsolverType(_solverType), idx(_index), maxPrintingAllowed(_maxPrintingAllowed), useChangeOfVariable(_useChangeOfVariable)
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
  
  CRNSnapshot crn;
  
  EncapsVarForGSL ev;
  
  NLSresults & results;

  int idx;
  
  int nlsolverType;
  
  bool maxPrintingAllowed;
  
  double tolerance;
  
  int maxiteration = 100;

  bool useChangeOfVariable;
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
