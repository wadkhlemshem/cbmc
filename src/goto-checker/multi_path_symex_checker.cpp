/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution

#include "multi_path_symex_checker.h"

#include <util/invariant.h>

#include <goto-symex/memory_model_pso.h>
#include <goto-symex/show_program.h>
#include <goto-symex/show_vcc.h>

#include "bmc_util.h"

multi_path_symex_checkert::multi_path_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_checkert(options, ui_message_handler),
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

propertiest multi_path_symex_checkert::operator()(const propertiest &properties)
{
  perform_symex();

  // coverage report
  std::string cov_out=options.get_option("symex-coverage-report");
  if(!cov_out.empty() &&
     symex.output_coverage_report(goto_model.get_goto_functions(), cov_out))
  {
    error() << "Failed to write symex coverage report to '"
            << cov_out << "'" << eom;
  }

  if(options.get_bool_option("show-vcc"))
  {
    namespacet ns(goto_model.get_symbol_table());
    show_vcc(options, ui_message_handler, ns, equation);
  }

  if(options.get_bool_option("program-only"))
  {
    namespacet ns(goto_model.get_symbol_table());
    show_program(ns, equation);
  }

  return properties_result_from_symex_target_equation(equation);
}

void multi_path_symex_checkert::perform_symex()
{
  namespacet ns(goto_model.get_symbol_table());

  auto get_goto_function = [this](const irep_idt &id) ->
    const goto_functionst::goto_functiont &
  {
    return goto_model.get_goto_function(id);
  };

  // perform symbolic execution
  symex.symex_from_entry_point_of(get_goto_function, symex_symbol_table);

  // add a partial ordering, if required
  if(equation.has_threads())
  {
    std::unique_ptr<memory_model_baset> memory_model =
      get_memory_model(options, ns);
    memory_model->set_message_handler(get_message_handler());
    (*memory_model)(equation);
  }

  statistics() << "size of program expression: "
               << equation.SSA_steps.size()
               << " steps" << eom;

  slice(symex, equation, ns, options, ui_message_handler);
}

goto_tracet multi_path_symex_checkert::build_error_trace() const
{
  // currently unsupported
  UNREACHABLE;
}
