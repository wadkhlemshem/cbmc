/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Path-Based Symbolic Execution

#include "paths_checker.h"

#include "bmc_util.h"

paths_checkert::paths_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : pathwise_symex_checkert(options, ui_message_handler, goto_model)
{
  solver_factoryt solvers(
    options,
    goto_model.get_symbol_table(),
    ui_message_handler,
    ui_message_handler.get_ui() == ui_message_handlert::uit::XML_UI);
  solver = solvers.get_solver();
}

goto_checkert::statust paths_checkert::operator()(propertiest &properties)
{
  return statust::DONE;
}

goto_tracet paths_checkert::build_error_trace() const
{
  goto_tracet goto_trace;
  return goto_trace;
}

void paths_checkert::output_error_witness(const goto_tracet &error_trace)
{
  namespacet ns(goto_model.get_symbol_table());
  output_graphml(error_trace, ns, options);
}
