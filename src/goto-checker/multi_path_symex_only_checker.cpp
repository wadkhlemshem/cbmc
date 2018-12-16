/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution Only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution only (no SAT solving)

#include "multi_path_symex_only_checker.h"

#include <util/invariant.h>

#include <goto-symex/memory_model_pso.h>
#include <goto-symex/show_program.h>
#include <goto-symex/show_vcc.h>

#include "bmc_util.h"

multi_path_symex_only_checkert::multi_path_symex_only_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : incremental_goto_checkert(options, ui_message_handler),
    goto_model(goto_model),
    symex(
      ui_message_handler,
      goto_model.get_symbol_table(),
      equation,
      options,
      path_storage)
{
  namespacet ns(goto_model.get_symbol_table());
  setup_symex(symex, ns, options, ui_message_handler);
}

incremental_goto_checkert::resultt multi_path_symex_only_checkert::
operator()(propertiest &properties)
{
  perform_symex();

  // coverage report
  std::string cov_out = options.get_option("symex-coverage-report");
  if(
    !cov_out.empty() &&
    symex.output_coverage_report(goto_model.get_goto_functions(), cov_out))
  {
    log.error() << "Failed to write symex coverage report to '" << cov_out
                << "'" << messaget::eom;
  }

  if(options.get_bool_option("show-vcc"))
  {
    namespacet ns(goto_model.get_symbol_table());
    show_vcc(options, ui_message_handler, equation);
  }

  if(options.get_bool_option("program-only"))
  {
    namespacet ns(goto_model.get_symbol_table());
    show_program(ns, equation);
  }

  update_properties_status_from_symex_target_equation(properties, equation);

  return resultt::DONE;
}

void multi_path_symex_only_checkert::perform_symex()
{
  namespacet ns(goto_model.get_symbol_table());

  auto get_goto_function =
    [this](const irep_idt &id) -> const goto_functionst::goto_functiont & {
    return goto_model.get_goto_function(id);
  };

  // perform symbolic execution
  symex.symex_from_entry_point_of(get_goto_function, symex_symbol_table);

  // add a partial ordering, if required
  // We won't be able to decide any properties by adding this,
  // but we'd like to see the entire SSA.
  if(equation.has_threads())
  {
    std::unique_ptr<memory_model_baset> memory_model =
      get_memory_model(options, ns);
    memory_model->set_message_handler(ui_message_handler);
    (*memory_model)(equation);
  }

  log.statistics() << "size of program expression: "
                   << equation.SSA_steps.size() << " steps" << messaget::eom;

  slice(symex, equation, ns, options, ui_message_handler);
}

goto_tracet multi_path_symex_only_checkert::build_error_trace() const
{
  // currently unsupported
  UNIMPLEMENTED;
}

void multi_path_symex_only_checkert::output_error_witness(const goto_tracet &)
{
  // unsupported
  UNIMPLEMENTED;
}

void multi_path_symex_only_checkert::output_proof()
{
  // unsupported
  UNIMPLEMENTED;
}
