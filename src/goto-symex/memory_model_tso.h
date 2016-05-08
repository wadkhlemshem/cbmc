/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_MEMORY_MODEL_TSO_H
#define CPROVER_MEMORY_MODEL_TSO_H

#include "memory_model_sc.h"

class memory_model_tsot:public memory_model_sct
{
public:
  inline explicit memory_model_tsot(const namespacet &_ns):
    memory_model_sct(_ns)
  {
  }

#ifdef REFINE_ENCODING
  virtual void operator()(
    symex_target_equationt& equation, 
    goto_tracet& trace, 
    goto_trace_SSA_step_mapt& step_map);

  virtual void operator()(symex_target_equationt &, bool lazy=false);
#else
  virtual void operator()(symex_target_equationt &equation);
#endif

protected:
  virtual exprt before(event_it e1, event_it e2);
  virtual bool program_order_is_relaxed(
    partial_order_concurrencyt::event_it e1,
    partial_order_concurrencyt::event_it e2) const;
  void program_order(symex_target_equationt &equation);
};

#endif

