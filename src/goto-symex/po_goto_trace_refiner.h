/*******************************************************************\

Module: Traces of GOTO Programs reduced to Shared Memory Accesses

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_GOTO_SYMEX_PO_GOTO_TRACE_REFINER_H
#define CPROVER_GOTO_SYMEX_PO_GOTO_TRACE_REFINER_H

#include <solvers/refinement/goto_trace_refiner.h>

#include "symex_target_equation.h"
#include "goto_symex_state.h"
#include "partial_order_concurrency.h"
#include "memory_model.h"

typedef std::vector<symex_target_equationt::SSA_stepst::const_iterator> 
  goto_trace_SSA_step_mapt;

class po_goto_trace_refinert : public goto_trace_refinert {
public:
  explicit po_goto_trace_refinert(const namespacet &_ns,
				symex_target_equationt &_equation,
			        memory_model_baset &_memory_model)
    :
    ns(_ns),
    equation(_equation),
    memory_model(_memory_model)
  {}
  
  virtual void operator()(prop_convt &prop_conv);

protected:
  const namespacet &ns;
  symex_target_equationt &equation;
  memory_model_baset &memory_model;

// builds a trace that stops at first failing assertion
  void build_po_goto_trace(
    const symex_target_equationt &target,
    const prop_convt &prop_conv,
    const namespacet &ns,
    const partial_order_concurrencyt::choice_mapt &choice_map,
    goto_tracet &goto_trace,
    goto_trace_SSA_step_mapt &steps_map);

// builds a trace that stops after given step
  void build_po_goto_trace(
    const symex_target_equationt &target,
    symex_target_equationt::SSA_stepst::const_iterator stop,
    const prop_convt &prop_conv,
    const namespacet &ns,
    const partial_order_concurrencyt::choice_mapt &choice_map,
    goto_tracet &goto_trace,
    goto_trace_SSA_step_mapt &steps_map);

};

#endif
