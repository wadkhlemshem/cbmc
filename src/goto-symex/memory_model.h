/*******************************************************************\

Module: Memory models for partial order concurrency

Author: Michael Tautschnig, michael.tautschnig@cs.ox.ac.uk

\*******************************************************************/

#ifndef CPROVER_MEMORY_MODEL_H
#define CPROVER_MEMORY_MODEL_H

#include "partial_order_concurrency.h"

typedef std::vector<symex_target_equationt::SSA_stepst::const_iterator> 
  goto_trace_SSA_step_mapt;

class memory_model_baset:public partial_order_concurrencyt
{
public:
  explicit memory_model_baset(const namespacet &_ns);
  virtual ~memory_model_baset();

#ifdef REFINE_ENCODING
  virtual void operator()(symex_target_equationt&, goto_tracet&, goto_trace_SSA_step_mapt&);
  virtual void operator()(symex_target_equationt &, bool lazy=false)=0;

  std::set<symex_target_equationt::SSA_stepst::const_iterator> 
    steps_of_interest;
#else
  virtual void operator()(symex_target_equationt &)=0;
#endif

  virtual const choice_mapt &get_choice_map() { return choice_symbols_rev; }
  
protected:
  // program order
  bool po(event_it e1, event_it e2);

  // produce fresh symbols  
  unsigned var_cnt;
  symbol_exprt nondet_bool_symbol(
    const std::string &prefix,
    const irep_idt &var1,
    const irep_idt &var2);
  
  // This gives us the choice symbol for an R-W pair;
  // built by the method below.
  typedef std::map<
    std::pair<event_it, event_it>, symbol_exprt> choice_symbolst;
  choice_symbolst choice_symbols;
  choice_mapt choice_symbols_rev;

  void read_from_some(symex_target_equationt &equation);
  void read_from(symex_target_equationt &equation);
  
  // maps thread numbers to an event list
  typedef std::map<unsigned, event_listt> per_thread_mapt;

#ifdef REFINE_ENCODING
  bool lazy;
  bool skip_lazy(event_listt::const_iterator);
#endif

};

#endif

