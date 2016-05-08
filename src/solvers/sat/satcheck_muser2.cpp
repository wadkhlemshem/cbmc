/*******************************************************************\

Module: Interface to MUSER2

Author: Peter Schrammel

\*******************************************************************/

#ifdef HAVE_MUSER2

#ifndef _MSC_VER
#include <inttypes.h>
#endif

#include <cassert>
#include <stack>
#include <iostream>

#include <util/threeval.h>

#include "satcheck_muser2.h"
#include <muser2_api.hh>

/*******************************************************************\

Function: satcheck_muser2t::satcheck_muser2t

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_muser2t::satcheck_muser2t(const char* solver_name)
  : order(MUSER2_RANDOM),
    cpu_time_limit(0),
    iter_limit(0)
{
  solver = new muser2();
  solver->set_sat_solver(solver_name);
  solver->init_all();
}

/*******************************************************************\

Function: satcheck_muser2t::satcheck_muser2t

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satcheck_muser2t::~satcheck_muser2t()
{
  delete solver;
}

/*******************************************************************\

Function: satcheck_muser2t::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_muser2t::l_get(literalt a) const
{
  return tvt(tvt::TV_UNKNOWN);
}

/*******************************************************************\

Function: satcheck_muser2t::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_muser2t::solver_text()
{
  return "MUSER2";
}

/*******************************************************************\

Function: satcheck_muser2t::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_muser2t::lcnf(const bvt &_bv)
{
  bvt bv;
  if(process_clause(_bv,bv)) //simplify
    return; //clause trivially satisfied, hence skip

  std::vector<int> tmp;
  tmp.reserve(bv.size());
  for(int i=0;i<bv.size();i++)
    tmp.push_back(bv[i].dimacs());
  solver->add_clause(&(tmp[0]),&(tmp[bv.size()-1]),0); //permanent

  clause_counter++;
}

/*******************************************************************\

Function: satcheck_muser2t::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_muser2t::prop_solve()
{
  // convert assumptions
  std::vector<int> tmp;
  tmp.reserve(assumptions.size());
  for(int i=0;i<assumptions.size();i++)
    tmp.push_back(assumptions[i].dimacs());
  for(int i=0;i<assumptions.size();i++)
  {
    solver->add_clause(&(tmp[i]),&(tmp[i]),assumptions[i].get());
#ifdef DEBUG
    std::cout << "gid: " << assumptions[i].get() 
              << " = " << tmp[i]
	      << std::endl;
#endif
  }

  {
    messaget::status() <<
//      _no_variables << " variables, " <<
      clause_counter << " clauses" << eom;
  }

#ifdef DEBUG
  solver->set_verbosity(1000,"MUSER: ");
#endif
  solver->set_order(order); 
  solver->set_cpu_time_limit(cpu_time_limit); 
  solver->set_iter_limit(iter_limit); 
  solver->init_run();

  switch(solver->test_sat())
  {
  case 10:  return P_SATISFIABLE;
  case 0 : return P_ERROR;
  case 20: break; 
  default: assert(false);
  }
#if 0
  int precise = 
#endif
    solver->compute_gmus();
#if 0
  std::cout << "MUS is" << (precise==0 ? " not" : "") 
	    << " precise" << std::endl;
#endif
  
  mus = solver->gmus_gids();
  solver->reset_run();
  //solver->reset_all(); //crashes?!
  
  messaget::status() <<
        "SAT checker: negated claim is UNSATISFIABLE, i.e., holds" << eom;
  return P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_muser2t::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_muser2t::set_assignment(literalt a, bool value)
{
  //not supported
}

/*******************************************************************\

Function: satcheck_muser2t::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_muser2t::is_in_conflict(literalt a) const
{
  for(int i=0; i<mus.size(); i++)
  {
#ifdef DEBUG
    std::cout << "MUS: " << mus[i] << std::endl;
#endif
    if(mus[i] == a.get())
      return true;
  }
  return false;
}

/*******************************************************************\

Function: satcheck_muser2t::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_muser2t::set_assumptions(const bvt &bv)
{
  assumptions = bv;

  forall_literals(it, bv)
    assert(!it->is_constant());
}

#endif


