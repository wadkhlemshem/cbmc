/*******************************************************************\

Module: Abstraction Refinement Loop

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#define PROFILING

#ifndef CPROVER_SOLVER_BV_REFINEMENT_H
#define CPROVER_SOLVER_BV_REFINEMENT_H

#include <langapi/language_ui.h>
#include <util/time_stopping.h>

#include <solvers/flattening/bv_pointers.h>

#include "goto_trace_refiner.h"

#define MAX_STATE 10000
#define COST_LEVEL_MAX 1
#define CLUSTER_SEP_FACTOR_MAX 8

class bv_refinementt:public bv_pointerst
{
public:
  bv_refinementt(const namespacet &_ns, propt &_prop,
		 goto_trace_refinert &_goto_trace_refiner);

  ~bv_refinementt();

  virtual decision_proceduret::resultt dec_solve();

  virtual std::string decision_procedure_text() const
  { return "refinement loop with "+prop.solver_text(); }
  
  typedef bv_pointerst SUB;

  // maximal number of times we refine a formula node
  unsigned max_node_refinement;

  // enable/disable refinements
  bool do_array_refinement;
  bool do_arithmetic_refinement;
  bool do_partial_order_refinement;
  bool do_partial_order_refinement_dp;
  bool do_refinement_slicing;
  
  using bv_pointerst::is_in_conflict;

  void set_ui(language_uit::uit _ui) { ui=_ui; }

  // we refine the partial order constraints
  void add_partial_order_constraint(const exprt &expr, 
				    const std::string &kind);
  bool has_wmm;

#ifdef LAZY_ENCODING_TEST
    typedef std::map<std::string,unsigned> kinds_counterst;
    kinds_counterst kinds_total, kinds_active;
#ifdef LAZY_ENCODING_STATISTICS
    kinds_counterst kinds_variables, kinds_clauses;
#endif
#endif

  // we refine the SSA itself
  void add_constraint(const exprt &expr, 
				    const std::string &kind);

protected:

  goto_trace_refinert &po_goto_trace_refiner;

  resultt prop_solve();

  // the list of operator approximations
  struct approximationt
  {
  public:
    explicit approximationt(unsigned _id_nr):id_nr(_id_nr)
    {
    }
  
    exprt expr;
    unsigned no_operands;

    bvt op0_bv, op1_bv, op2_bv, result_bv;
    mp_integer op0_value, op1_value, op2_value, result_value;

    bvt under_assumptions;
    bvt over_assumptions;

    // the kind of under- or over-approximation    
    unsigned under_state, over_state;
    
    approximationt():under_state(0), over_state(0)
    {
    }
    
    std::string as_string() const;
    
    void add_over_assumption(literalt l);
    void add_under_assumption(literalt l);
    
    unsigned id_nr;
  };
  
  typedef std::list<approximationt> approximationst;
  approximationst approximations;
  
  approximationt &add_approximation(const exprt &expr, bvt &bv);
  void check_SAT(approximationt &approximation);
  void check_UNSAT(approximationt &approximation);
  void initialize(approximationt &approximation);
  void get_values(approximationt &approximation);
  bool is_in_conflict(approximationt &approximation);
  
  void check_SAT();
  void check_UNSAT();
  bool progress;
  
  // we refine the theory of arrays
  virtual void post_process_arrays();
  void arrays_overapproximated();
  
  // we refine expensive arithmetic
  virtual void convert_mult(const exprt &expr, bvt &bv);
  virtual void convert_div(const exprt &expr, bvt &bv);
  virtual void convert_mod(const exprt &expr, bvt &bv);
  virtual void convert_floatbv_op(const exprt &expr, bvt &bv);


  // for collecting statistics
  virtual void set_to(const exprt &expr, bool value);

  // overloading
  virtual void set_assumptions(const bvt &_assumptions);

  // we refine the partial order constraints
  void partial_order_constraints_overapproximated();

  // we refine the whole SSA
  void constraints_overapproximated();

  typedef struct {
    exprt constraint;
    std::string kind;
    unsigned cost;
  } lazy_constraintt;
  typedef std::list<lazy_constraintt> 
    lazy_constraintst;

  typedef struct {
    lazy_constraintst::iterator original;
    exprt simplified;
  } acc_constraintt;
  typedef std::vector<acc_constraintt> acc_constraintst;

  lazy_constraintst lazy_partial_order_constraints;
  lazy_constraintst constraints;
  unsigned cost_level, cluster_sep_factor;
  void activate_partial_order_constraint(
    lazy_constraintst::iterator it, unsigned &nb_active);
  bool is_assignment_coherent(const exprt &expr) const;
  bool expr_contains_arrays(const exprt &expr) const;
  bool expr_contains_symbols(const exprt &expr) const;
  bool is_trivially_satisfied(const exprt &expr);

  // for incremental solving, e.g. all properties
  bvt parent_assumptions;

  // use gui format
  language_uit::uit ui;

#ifdef PROFILING
  time_periodt time_main_solver;
  time_periodt time_sat_check;
  time_periodt time_clustering;
#endif
};

#endif
