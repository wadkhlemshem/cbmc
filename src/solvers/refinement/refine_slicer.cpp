/*******************************************************************\

Module: Refinement Slicer

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

//#define DEBUG

#include <climits>
#include <langapi/language_util.h>
#include <util/std_expr.h>
#include <util/base_type.h>
#include <solvers/sat/satcheck.h>
#ifdef HAVE_MUSER2
#include <solvers/sat/satcheck_muser2.h>
#endif

#include <util/cluster.h>
#include <util/find_symbols.h>

#include "bv_refinement.h"

/*******************************************************************\

Function: bv_refinementt::add_constraint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::add_constraint(const exprt &expr,
			 	    const std::string &kind)
{
  if(do_refinement_slicing)
  {
    // don't add garbage
    if (expr == true_exprt())
      return;

    // let's add these kinds of constraints right away
    if(false
       //kind == "assign"  
       // kind == "guard"  
       )
    {
#ifdef LAZY_ENCODING_TEST
	kinds_total[kind]++;
	kinds_active[kind]++;
#endif
      return set_to_true(expr);
    }

    constraints.push_back(lazy_constraintt());
    lazy_constraintt &c = constraints.back();
    c.constraint = expr;
    c.kind = kind;
    c.cost = 0; //avoid holes in cost levels!
    if(expr_contains_arrays(expr)) c.cost = 1;
    else if(c.kind == "guard") c.cost = 0;
    else if(c.kind == "assign") c.cost = 0;

#ifdef LAZY_ENCODING_TEST
    kinds_total[kind]++;
#endif
  }
  else // add everything
    set_to_true(expr);
}

/*******************************************************************\

Function: bv_refinementt::constraints_overapproximated

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void bv_refinementt::constraints_overapproximated()
{
  if(!do_refinement_slicing) 
    return;

  acc_constraintst acc_constraints;

  unsigned nb_active = 0;
#ifdef LAZY_ENCODING_TEST
  kinds_counterst new_kinds_active;
#endif

#if 1
  unsigned number_of_single_constraints = 0;
#endif


  lazy_constraintst::iterator it = 
    constraints.begin();
  while(it != constraints.end())
  {
    if(it->cost>cost_level) 
    {
      ++it;
      continue;
    }   

#ifdef DEBUG
    std::cout << "checking constraint [" 
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

    // accumulate constraints containing free variables
    //   and solve them together
    // Remark: Checking satisfiability of the constraint 
    //   before looking for free variables is slower.
    if(expr_contains_symbols(simplified))
    {
      acc_constraints.push_back(acc_constraintt());
      acc_constraintt &acc = acc_constraints.back();
      acc.original = it++;
      acc.simplified = simplified;
#ifdef DEBUG
      std::cout << " ---> accumulate" << std::endl;
#endif
      continue;
    }

    //solve single constraints without free choices
    satcheckt local_sat_check2;
    bv_pointerst local_solver2(ns,local_sat_check2);
    local_solver2 << simplified;
#if 1
    number_of_single_constraints++;
#endif
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

#ifdef LAZY_ENCODING_TEST
      kinds_active[it->kind]++;
      new_kinds_active[it->kind]++;
#endif
      set_to_true(it->constraint);
      nb_active++;
      constraints.erase(it++);
      break;
    default:
      assert(false);
    }
  }
 
#if 1
  unsigned number_of_active_single_constraints = nb_active;
  std::cout << "     single constraints: " << number_of_single_constraints << " ---> " << nb_active << std::endl;
#endif

  //solve accumulated formula
  if(acc_constraints.size()>0)
  {
    typedef acc_constraintst::iterator tag_typet;

#ifdef CLUSTERING
    //do clustering
#ifdef PROFILING
    time_periodt t0(current_time().get_t());
#endif    
    clustert<irep_idt,tag_typet> cluster(UINT_MAX,UINT_MAX);
    for(acc_constraintst::iterator it = 
	  acc_constraints.begin(); it != acc_constraints.end(); ++it)
    {
      find_symbols_sett s;
      find_symbols(it->simplified,s);
      std::vector<irep_idt> ss;
      ss.reserve(s.size());
      for(find_symbols_sett::const_iterator i=s.begin();
	  i!=s.end(); ++i) ss.push_back(*i);
      cluster.add(ss,1,it);
    }
#if 1
    std::cout << "max weight = " << cluster.get_max_weight() << std::endl;
#endif
    unsigned min_weight = cluster.get_max_weight()/cluster_sep_factor;
    if(min_weight == 0)
    {
      cluster_sep_factor = UINT_MAX;
      min_weight = 0;
    }
    cluster(min_weight);
    std::vector<std::vector<tag_typet> > clusters;
    cluster.get_tags(clusters);
#ifdef PROFILING
      time_periodt t1(current_time().get_t());
      time_clustering += (t1-t0); 
#endif
      
#else //no CLUSTERING
    std::vector<std::vector<tag_typet> > clusters;
    clusters.resize(1);
    clusters[0].reserve(acc_constraints.size());
    for(acc_constraintst::iterator it = 
	  acc_constraints.begin(); it != acc_constraints.end(); ++it)
      clusters[0].push_back(it);
#endif 

    //make sure nothing was lost
    unsigned count = 0;
    for(std::vector<std::vector<tag_typet> >::const_iterator
	  it = clusters.begin(); it!=clusters.end(); ++it)
    {
      count += it->size();
    }
    assert(count == acc_constraints.size());

    //solve for each cluster
    for(std::vector<std::vector<tag_typet> >::const_iterator
	  it = clusters.begin(); it!=clusters.end(); ++it)
    {
      if(it->size()<=1) //that should be sound
	continue;
#if 1
      std::cout << "cluster of size " << it->size() << std::endl;
#endif
      
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
      acc_assumptions.reserve(it->size());
      numbering<acc_constraintst::iterator> acc_map;

      for(std::vector<tag_typet>::const_iterator 
	    c_it = it->begin(); c_it != it->end(); ++c_it)
      {
	literalt l = local_solver1.convert((*c_it)->simplified);
	if(l.is_true())
	  continue;
	if(l.is_false()) // simplifier has done the job
	{
#if 1
  	  std::cout << "accumulated ---> UNSAT5" << std::endl;
#endif
#ifdef LAZY_ENCODING_TEST
	  kinds_active[(*c_it)->original->kind]++;
	  new_kinds_active[(*c_it)->original->kind]++;
#endif
	  set_to_true((*c_it)->original->constraint);
	  nb_active++;
	  constraints.erase((*c_it)->original);
	  continue;
	}
	acc_assumptions.push_back(l);
#ifndef DO_CEX_MINIMIZATION
	local_solver1 << literal_exprt(l);
#endif
	acc_map.number((*c_it));
      }

      // solve the cluster
#ifdef DO_CEX_MINIMIZATION
      local_solver1.set_assumptions(acc_assumptions);
#endif
      switch(local_solver1())
      {
      case decision_proceduret::D_SATISFIABLE:
#ifdef DEBUG
	std::cout << "accumulated ---> SAT4" << std::endl;
#endif
	break; 
      case decision_proceduret::D_UNSATISFIABLE:
#if 1
	std::cout << "accumulated ---> UNSAT4" << std::endl;
#endif
	for(unsigned i=0; i<acc_assumptions.size(); i++)
	{
	  //add minimized number of constraints (seems to be a bad idea in practice)
#ifdef DO_CEX_MINIMIZATION
	  if(local_solver1.is_in_conflict(acc_assumptions[i]))
#endif
	  {
#ifdef DEBUG
	    std::cout << "adding constraint [" 
		      << acc_map[i]->original->kind << "]: " 
		      << from_expr(ns,"",acc_map[i]->original->constraint)
		      << std::endl;
#endif      

#ifdef LAZY_ENCODING_TEST
	    kinds_active[acc_map[i]->original->kind]++;
	    new_kinds_active[acc_map[i]->original->kind]++;
#endif
	    set_to_true(acc_map[i]->original->constraint);
	    nb_active++;
	    constraints.erase(acc_map[i]->original);
	  }
	}
	break;
      default:
	assert(false);
      }
    }
  }

#if 1
  std::cout << "accumulated constraints: " << acc_constraints.size() << " ---> " << (nb_active-number_of_active_single_constraints) << std::endl;
#endif

  std::cout << "BV-Refinement: " << nb_active << " constraints become active" << std::endl;
  std::cout << "BV-Refinement: " << constraints.size() << " inactive constraints" << std::endl;

#ifdef LAZY_ENCODING_TEST
  std::cout << "Constraints become active: " << std::endl; 
  for(kinds_counterst::iterator kit = new_kinds_active.begin();
      kit != new_kinds_active.end(); ++kit)
  {
    std::cout << "  " << kit->first << ": " 
	      << kit->second  << std::endl;
  }
#endif

  if (nb_active > 0)
    progress = true;
  else
  {
    if(cost_level<COST_LEVEL_MAX)
      { 
        cost_level++;
	progress = true;
      }
    else if(cluster_sep_factor<CLUSTER_SEP_FACTOR_MAX)
      { 
        cluster_sep_factor <<= 1;
	progress = true;
      }
  }
}

