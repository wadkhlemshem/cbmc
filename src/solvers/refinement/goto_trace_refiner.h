/*******************************************************************\

Module: Traces of GOTO Programs reduced to Shared Memory Accesses

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_SOLVER_GOTO_TRACE_REFINER_H
#define CPROVER_SOLVER_GOTO_TRACE_REFINER_H

#include <solvers/prop/prop_conv.h>

class goto_trace_refinert {
public:
 
  virtual void operator()(prop_convt &prop_conv) { assert(false); }

};

#endif
