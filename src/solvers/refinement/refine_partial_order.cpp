/*******************************************************************\

Module: Lazy Partial Order Encoding

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#define DEBUG

#ifdef DEBUG
#include <langapi/language_util.h>
#endif

#include <util/find_symbols.h>
#include <util/std_expr.h>
#include <util/base_type.h>
#include <solvers/sat/satcheck.h>
#ifdef HAVE_MUSER2
#include <solvers/sat/satcheck_muser2.h>
#endif

#include "bv_refinement.h"

/*******************************************************************\

Function: bv_refinementt::add_partial_order_constraint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::add_partial_order_constraint(const exprt &expr,
						  const std::string &kind)
{
  if(do_partial_order_refinement)
  {
    // don't add garbage
    if (expr == true_exprt())
      return;

#ifdef LAZY_ENCODING_STATISTICS2
    typedef satcheck_minisat_no_simplifiert satt;
    satt::statisticst s1 = dynamic_cast<satt *>(&prop)->get_statistics();
    set_to_true(expr);
    satt::statisticst s2 = dynamic_cast<satt *>(&prop)->get_statistics();
    kinds_variables[kind] += (s2.variables - s1.variables);
    kinds_clauses[kind] += (s2.clauses - s1.clauses);
#else
    // add array constraints immediately to avoid problems
    //    with the array post processing
    if(expr_contains_arrays(expr))
      return set_to_true(expr);
    
    // let's add these kinds of constraints right away
    if(kind == "thread-spawn"  //~20% needed on average
       || (!do_partial_order_refinement && kind == "po")
       || (do_partial_order_refinement && kind == "po" && !has_wmm) //~40% needed for SC, ~5% for WMMs
//        || kind == "rf"        //~65% needed on average
//        || kind == "rf-order" //~45% needed on average
        || kind == "rf-some"   //~80% needed on average
//        || kind == "rfi"       //~60% needed on average
//       || kind == "fr"       //~15% needed on average
//        || kind == "ws-ext"   //~10% needed on average
       )
    {
#ifdef LAZY_ENCODING_TEST
	kinds_total[kind]++;
	kinds_active[kind]++;
#endif

#ifdef DEBUG
	std::cout << "adding constraint [" 
		  << kind << "]: " 
		  << from_expr(ns,"",expr)
		  << std::endl;
#endif      

      return set_to_true(expr);
    }
    
    lazy_partial_order_constraints.push_back(lazy_constraintt());
    lazy_constraintt &c = lazy_partial_order_constraints.back();
    c.constraint = expr;
    c.kind = kind;
#endif
    
#ifdef LAZY_ENCODING_TEST
    kinds_total[kind]++;
#endif
  }
  else
    set_to_true(expr);

}

/*******************************************************************\

Function: bv_refinementt::activate_partial_order_constraints

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::activate_partial_order_constraint(
  lazy_constraintst::iterator it, unsigned &nb_active)
{
#ifdef DEBUG
  std::cout << "adding constraint [" 
	    << it->kind << "]: " 
	    << from_expr(ns,"",it->constraint)
	    << std::endl;
  find_symbols_sett symbols;
  find_symbols(it->constraint,symbols);
  std::cout << "events:";
  for(find_symbols_sett::const_iterator it = symbols.begin();
      it != symbols.begin(); ++it)
  {
    std::cout << " " << *it;
  }
  std::cout << std::endl;
#endif      

#ifdef LAZY_ENCODING_TEST
  kinds_active[it->kind]++;
#endif
  set_to_true(it->constraint);
  nb_active++;
  lazy_partial_order_constraints.erase(it++);
}


/*******************************************************************\

Function: bv_refinementt::partial_order_constraints_overapproximated

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::partial_order_constraints_overapproximated()
{
  if(!do_partial_order_refinement) 
    return;

  unsigned nb_active = 0;

  if(!do_partial_order_refinement_dp)
  {
#ifndef PO_CONSTRAINT_CACHE
    lazy_partial_order_constraints.clear();
#endif

    // build goto trace and generate constraints
    po_goto_trace_refiner(*this);
   
#ifndef DO_CEX_MINIMIZATION
    for(lazy_constraintst::iterator 
	  it = lazy_partial_order_constraints.begin();
	it != lazy_partial_order_constraints.end(); )
    {
      activate_partial_order_constraint(it,nb_active);  
    }
    assert(lazy_partial_order_constraints.empty());
    std::cout << "BV-Refinement: " << nb_active << " partial order constraints become active" << std::endl;
    std::cout << "BV-Refinement: " << lazy_partial_order_constraints.size() << " inactive partial order constraints" << std::endl;
    if (nb_active > 0)
      progress = true;

    return;
#endif
  }
  
#ifdef HAVE_MUSER2
  satcheck_muser2t local_sat_check1(MUSER2_MINISAT2);
  local_sat_check1.set_order(MUSER2_MAXMIN);
  local_sat_check1.set_cpu_time_limit(0);
  local_sat_check1.set_iter_limit(0);
#else
  satcheckt local_sat_check1;
#endif
  bv_pointerst local_solver1(ns,local_sat_check1);
  bvt acc_assumptions;
  std::vector<lazy_constraintst::iterator> acc_constraints;

  lazy_constraintst::iterator it = 
    lazy_partial_order_constraints.begin();
  while(it != lazy_partial_order_constraints.end())
  {
#ifdef DEBUG
    std::cout << "checking partial-order constraint [" 
      << it->kind << "]: " 
      << from_expr(ns,"",it->constraint);
#endif      

    // some simplifications
    if(is_trivially_satisfied(it->constraint))
    {
      ++it;
      continue;
    }

    // substitute countermodel
    exprt simplified = get(it->constraint);
#ifdef DEBUG
    std::cout << std::endl << "constraint to evaluate: " 
      << from_expr(ns,"",simplified) 
      << std::endl;
#endif

    // accumulate constraints containing free booleans
    //   (choice variables) and solve them together
    // Remark: Checking satisfiability of the constraint 
    //   before looking for free variables is slower.
    if(expr_contains_symbols(simplified))
    {
      literalt l = local_solver1.convert(simplified);
      if(l.is_true()) // simplifier may have done the job...
      {
#ifdef DEBUG
	std::cout << " ---> SAT5" << std::endl;
#endif
	++it;
      }
      else if(l.is_false())
      {
#ifdef DEBUG
	std::cout << " ---> UNSAT5" << std::endl;
#endif

        activate_partial_order_constraint(it,nb_active);
      }
      else
      {
	acc_assumptions.push_back(l);
	acc_constraints.push_back(it++);
#ifdef DEBUG
	std::cout << " ---> accumulate" << std::endl;
#endif
      }
    }
    else //solve single constraints without free choices
    {
      satcheckt local_sat_check2;
      bv_pointerst local_solver2(ns,local_sat_check2);
      local_solver2 << simplified;
      switch(local_solver2())
      {
      case decision_proceduret::D_SATISFIABLE:
        ++it;
#ifdef DEBUG
        std::cout << " ---> SAT3" << std::endl;
#endif
	break; 
      case decision_proceduret::D_UNSATISFIABLE:
#ifdef DEBUG
        std::cout << " ---> UNSAT3" << std::endl;
#endif

        activate_partial_order_constraint(it,nb_active);
	break;
      default:
	assert(false);
      }
    }
#ifdef MINCORE_ONLY
    if(nb_active>0) break;
#endif
  }
  //solve accumulated formula
  if(
#ifdef MINCORE_ONLY
     nb_active==0 &&
#endif
     acc_assumptions.size()>0)
  {
    local_solver1.set_assumptions(acc_assumptions);
    switch(local_solver1())
    {
    case decision_proceduret::D_SATISFIABLE:
#ifdef DEBUG
      std::cout << "accumulated ---> SAT4" << std::endl;
#endif
      break; 
    case decision_proceduret::D_UNSATISFIABLE:
#ifdef DEBUG
      std::cout << "accumulated ---> UNSAT4" << std::endl;
#endif
      for(unsigned i=0; i<acc_assumptions.size(); i++)
      {
	if(local_solver1.is_in_conflict(acc_assumptions[i]))
	{
	  activate_partial_order_constraint(acc_constraints[i],nb_active);
	}
      }
      break;
    default:
      assert(false);
    }
  }

  std::cout << "BV-Refinement: " << nb_active << " partial order constraints become active" << std::endl;
  std::cout << "BV-Refinement: " << lazy_partial_order_constraints.size() << " inactive partial order constraints" << std::endl;
  if (nb_active > 0)
    progress = true;
#ifdef COST_HEURISTICS
  else if(cost_level++<COST_LEVEL_MAX)
    progress = true;
#endif
}

/*******************************************************************\

Function: bv_refinementt::expr_contains_arrays

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool bv_refinementt::expr_contains_arrays(const exprt &expr) const
{
  if (expr.type().id() == ID_array)
    return true;
  for(exprt::operandst::const_iterator it = expr.operands().begin();
      it != expr.operands().end(); ++it)
  {
    if(expr_contains_arrays(*it))
      return true;
  }
  return false;
}

/*******************************************************************\

Function: bv_refinementt::expr_contains_symbols

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool bv_refinementt::expr_contains_symbols(const exprt &expr) const
{
  if (expr.id() == ID_symbol)
    return true;
  for(exprt::operandst::const_iterator it = expr.operands().begin();
      it != expr.operands().end(); ++it)
  {
    if(expr_contains_symbols(*it))
      return true;
  }
  return false;
}

/*******************************************************************\

Function: bv_refinementt::is_assignment_coherent

  Inputs:

 Outputs:

 Purpose: array assignments in the model may have finite size, 
       but the other side of the equality has size infinity
       let's add such equalities to the formula

\*******************************************************************/

bool bv_refinementt::is_assignment_coherent(const exprt &expr) const
{
  if (expr.id() == ID_equal)
  {
    if(!base_type_eq(expr.op0().type(), expr.op1().type(), ns))
      return false;
    return true;
  }
  for(exprt::operandst::const_iterator it = expr.operands().begin();
      it != expr.operands().end(); ++it)
  {
    if(!is_assignment_coherent(*it))
      return false;
  }
  return true;
}

/*******************************************************************\

Function: bv_refinementt::is_trivially_satisfied

  Inputs:

 Outputs:

 Purpose: some simplifications

\*******************************************************************/

bool bv_refinementt::is_trivially_satisfied(const exprt &expr) 
{
#if 0 //I have never observed this one, but maybe for arrays
  if (expr.id() == ID_implies)
  {
    const implies_exprt &imp = to_implies_expr(expr);
    assert (imp.operands().size() == 2);
    exprt implies_simplified = get(imp.op0());
    if (implies_simplified == false_exprt())
    {
#ifdef DEBUG
      std::cout << " ---> SAT1" << std::endl;
#endif
      return true;
    }
  }
#endif

  if (expr.id() == ID_or)
  {
    const or_exprt &orexp = to_or_expr(expr);
    for(exprt::operandst::const_iterator oit = orexp.operands().begin();
        oit != orexp.operands().end(); ++oit)
    {
      exprt o = get(*oit);
      if (o == true_exprt())
      {
#ifdef DEBUG
	std::cout << " ---> SAT2" << std::endl;
#endif
	return true;
      }
    }
  }
  return false;
}
