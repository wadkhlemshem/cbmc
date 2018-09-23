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
  solver_factoryt solvers(
    options,
    goto_model.get_symbol_table(),
    ui_message_handler,
    ui_message_handler.get_ui() == ui_message_handlert::uit::XML_UI);
  solver = solvers.get_solver();
}

goto_checkert::statust bmc_checkert::operator()(propertiest &properties)
{
  perform_symex();

  properties |= properties_result_from_symex_target_equation(equation);

  return statust::DONE;
}

goto_tracet bmc_checkert::build_error_trace() const
{
  namespacet ns(goto_model.get_symbol_table());
  goto_tracet error_trace;
  ::build_error_trace(error_trace, ns, equation, solver->prop_conv(), ui_message_handler);
  return error_trace;
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