/*******************************************************************\

Module: Goto Checker using Pathwise Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Pathwise Symbolic Execution

#include "pathwise_symex_checker.h"

#include <util/invariant.h>

pathwise_symex_checkert::pathwise_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_checkert(options, ui_message_handler),
    goto_model(goto_model)
{
}

goto_checkert::statust pathwise_symex_checkert::operator()(propertiest &properties)
{
  safety_checkert::resultt final_result = safety_checkert::resultt::UNKNOWN;
  safety_checkert::resultt tmp_result = safety_checkert::resultt::UNKNOWN;
  std::unique_ptr<path_storaget> worklist;
  std::string strategy = opts.get_option("exploration-strategy");
  INVARIANT(
    path_strategy_chooser.is_valid_strategy(strategy),
    "Front-end passed us invalid path strategy '" + strategy + "'");
  worklist = path_strategy_chooser.get(strategy);
  while(!worklist->empty())
  {
    if(tmp_result != safety_checkert::resultt::PAUSED)
      message.status() << "___________________________\n"
                       << "Starting new path (" << worklist->size()
                       << " to go)\n"
                       << message.eom;
    solver_factoryt solvers(
      opts,
      symbol_table,
      ui,
      ui.get_ui() == ui_message_handlert::uit::XML_UI);
    std::unique_ptr<solver_factoryt::solvert> cbmc_solver;
    cbmc_solver = solvers.get_solver();
    prop_convt &pc = cbmc_solver->prop_conv();
    path_storaget::patht &resume = worklist->peek();
    path_explorert pe(
      opts,
      symbol_table,
      ui,
      pc,
      resume.equation,
      resume.state,
      *worklist,
      callback_after_symex);
    if(driver_configure_bmc)
      driver_configure_bmc(pe, symbol_table);
    tmp_result = pe.run(model);

    if(
      tmp_result == safety_checkert::resultt::UNSAFE &&
      options.get_bool_option("stop-on-fail") && options.is_set("paths"))
    {
      worklist->clear();
      return CPROVER_EXIT_VERIFICATION_UNSAFE;
    }

    if(tmp_result != safety_checkert::resultt::PAUSED)
      final_result &= tmp_result;
    worklist->pop();
  }

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

  properties |= properties_result_from_symex_target_equation(equation);

  return statust::DONE;
}

void pathwise_symex_checkert::perform_symex()
{
  namespacet ns(goto_model.get_symbol_table());

  auto get_goto_function = [this](const irep_idt &id) ->
    const goto_functionst::goto_functiont &
  {
    return goto_model.get_goto_function(id);
  };

  // perform symbolic execution
  symex.resume_symex_from_saved_state(
    get_goto_function, saved_state, &equation, symex_symbol_table);

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

goto_tracet pathwise_symex_checkert::build_error_trace() const
{
  // currently unsupported
  UNREACHABLE;
}
