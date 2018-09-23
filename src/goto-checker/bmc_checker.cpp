/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking

#include "bmc_checker.h"

#include "bmc_util.h"

bmc_checkert::bmc_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : multi_path_symex_checkert(options, ui_message_handler, goto_model)
{
}

goto_checkert::statust bmc_checkert::operator()(propertiest &properties)
{
  return statust::DONE;
}

goto_tracet bmc_checkert::build_error_trace() const
{
  goto_tracet goto_trace;
  return goto_trace;
}

void bmc_checkert::output_proof()
{
  namespacet ns(goto_model.get_symbol_table());
  output_graphml(equation, ns, options);
}

void bmc_checkert::output_error_witness(const goto_tracet &error_trace)
{
  namespacet ns(goto_model.get_symbol_table());
  output_graphml(error_trace, ns, options);
}