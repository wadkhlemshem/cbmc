/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <iostream>

#include <util/i2string.h>
#include <util/xml.h>

#include "bv_refinement.h"

/*******************************************************************\

Function: bv_refinementt::bv_refinementt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_refinementt::bv_refinementt(const namespacet &_ns, propt &_prop,
		 goto_trace_refinert &_po_goto_trace_refiner):
  bv_pointerst(_ns, _prop),
  max_node_refinement(5),
  do_array_refinement(true),
  do_arithmetic_refinement(true),
  do_partial_order_refinement(false),
  do_partial_order_refinement_dp(false),
  do_refinement_slicing(false),
  has_wmm(false),
  po_goto_trace_refiner(_po_goto_trace_refiner)
#ifdef PROFILING
  ,time_main_solver(0)
  ,time_sat_check(0)
  ,time_clustering(0)
#endif
{
  // check features we need
  assert(prop.has_set_assumptions());
  assert(prop.has_set_to());
  assert(prop.has_is_in_conflict());
}

/*******************************************************************\

Function: bv_refinementt::~bv_refinementt

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bv_refinementt::~bv_refinementt()
{
}

/*******************************************************************\

Function: bv_refinementt::dec_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt bv_refinementt::dec_solve()
{
  // do the usual post-processing
  status() << "BV-Refinement: post-processing" << eom;
  post_process();

  debug() << "Solving with " << prop.solver_text() << eom;
  
  unsigned iteration=0;
  cost_level=0;
  cluster_sep_factor = 2;
  
  // now enter the loop
  while(true)
  {
    iteration++;
  
    status() << "BV-Refinement: iteration " << iteration << eom;

    // output the very same information in a structured fashion
    if(ui==ui_message_handlert::XML_UI)
    {
      xmlt xml("refinement-iteration");
      xml.data=i2string(iteration);
      std::cout << xml << '\n';
    }
#ifdef PROFILING
    time_periodt t0(current_time().get_t());
#endif
    switch(prop_solve())
    {
    case D_SATISFIABLE: {
#ifdef PROFILING
      time_periodt t1(current_time().get_t());
      time_main_solver += (t1-t0); 
#endif
      check_SAT();
#ifdef PROFILING
      time_sat_check += (time_periodt(current_time().get_t())-t1);
#endif
      if(!progress)
      {
        status() << "BV-Refinement: got SAT, and it simulates => SAT" << eom;
        status() << "Total iterations: " << iteration << eom;
#ifdef PROFILING
      status() << "PROFILING: main_solver: " << time_main_solver << eom;
      status() << "PROFILING: sat_check: " << (time_sat_check-time_clustering) << eom;
      status() << "PROFILING: clustering: " << time_clustering << eom;
#endif
        return D_SATISFIABLE;
      }
      else
        status() << "BV-Refinement: got SAT, and it is spurious, refining" << eom;
      break; }

    case D_UNSATISFIABLE:
#ifdef PROFILING
      time_main_solver += (time_periodt(current_time().get_t())-t0);
#endif
      check_UNSAT();
      if(!progress)
      {
        status() << "BV-Refinement: got UNSAT, and the proof passes => UNSAT" << eom;
        status() << "Total iterations: " << iteration << eom;
#ifdef PROFILING
      status() << "PROFILING: main_solver: " << time_main_solver << eom;
      status() << "PROFILING: sat_check: " << (time_sat_check-time_clustering) << eom;
      status() << "PROFILING: clustering: " << time_clustering << eom;
#endif
        return D_UNSATISFIABLE;
      }
      else
        status() << "BV-Refinement: got UNSAT, and the proof fails, refining" << eom;
      break;
    
    default:
      return D_ERROR;
    }
  }
}

/*******************************************************************\

Function: bv_refinementt::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

decision_proceduret::resultt bv_refinementt::prop_solve()
{
  // this puts the underapproximations into effect
  bvt assumptions = parent_assumptions;

  for(approximationst::const_iterator
      a_it=approximations.begin();
      a_it!=approximations.end();
      a_it++)
  {
    assumptions.insert(
      assumptions.end(),
      a_it->over_assumptions.begin(), a_it->over_assumptions.end());
    assumptions.insert(
      assumptions.end(),
      a_it->under_assumptions.begin(), a_it->under_assumptions.end());
  }

  prop.set_assumptions(assumptions);
  propt::resultt result=prop.prop_solve();
  prop.set_assumptions(parent_assumptions);
 
  switch(result)
  {
   case propt::P_SATISFIABLE: return D_SATISFIABLE;
   case propt::P_UNSATISFIABLE: return D_UNSATISFIABLE;
   default: return D_ERROR;
  }
}

/*******************************************************************\

Function: bv_refinementt::check_SAT

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::check_SAT()
{
  progress=false;
  
  arrays_overapproximated();
  partial_order_constraints_overapproximated();
  constraints_overapproximated();

  for(approximationst::iterator
      a_it=approximations.begin();
      a_it!=approximations.end();
      a_it++)
    check_SAT(*a_it);
}

/*******************************************************************\

Function: bv_refinementt::check_UNSAT

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::check_UNSAT()
{
  progress=false;

  for(approximationst::iterator
      a_it=approximations.begin();
      a_it!=approximations.end();
      a_it++)
    check_UNSAT(*a_it);
}

/*******************************************************************\

Function: bv_refinementt::set_to

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::set_to(const exprt &expr, bool value)
{
  #if 0
  unsigned prev=prop.no_variables();
  SUB::set_to(expr, value);
  unsigned n=prop.no_variables()-prev;
  std::cout << n << " EEE " << expr.id() << "@" << expr.type().id();
  forall_operands(it, expr) std::cout << " " << it->id() << "@" << it->type().id();
  if(expr.id()=="=" && expr.operands().size()==2)
    forall_operands(it, expr.op1()) std::cout << " " << it->id() << "@" << it->type().id();
  std::cout << std::endl;
  #else
  SUB::set_to(expr, value);
  #endif
}

/*******************************************************************\

Function: bv_refinementt::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::set_assumptions(const bvt &_assumptions) {
  parent_assumptions = _assumptions;
  prop.set_assumptions(_assumptions);
}
