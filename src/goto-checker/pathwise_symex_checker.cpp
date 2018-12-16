/*******************************************************************\

Module: Goto Checker using Pathwise Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Pathwise Symbolic Execution

#include "pathwise_symex_checker.h"

#include <goto-symex/memory_model_pso.h>
#include <goto-symex/path_storage.h>
#include <goto-symex/show_program.h>
#include <goto-symex/show_vcc.h>

#include <util/invariant.h>

#include "bmc_util.h"
#include "symex_bmc.h"

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
  while(!worklist->empty())
  {
    log.status() << "___________________________\n"
             << "Starting new path (" << worklist->size()
             << " to go)\n"
             << messaget::eom;
    path_storaget::patht &resume = worklist->peek();
    symbol_tablet symex_symbol_table;
    symex_bmct symex(
      ui_message_handler,
      goto_model.get_symbol_table(),
      resume.equation,
      options,
      *worklist);

    namespacet ns(goto_model.get_symbol_table(), symex_symbol_table);
    setup_symex(symex, ns, options, ui_message_handler);
    perform_symex(symex, resume, symex_symbol_table);

    // coverage report
    std::string cov_out=options.get_option("symex-coverage-report");
    if(!cov_out.empty() &&
       symex.output_coverage_report(goto_model.get_goto_functions(), cov_out))
    {
      log.error() << "Failed to write symex coverage report to '"
              << cov_out << "'" << messaget::eom;
    }

    if(options.get_bool_option("show-vcc"))
    {
      show_vcc(options, ui_message_handler, resume.equation);
    }

    if(options.get_bool_option("program-only"))
    {
      show_program(ns, resume.equation);
    }

    update_properties_result_from_symex_target_equation(resume.equation, properties);

    worklist->pop();
  }

  return statust::DONE;
}

void pathwise_symex_checkert::perform_symex(
  symex_bmct &symex, path_storaget::patht &resume, symbol_tablet &symex_symbol_table)
{
  namespacet ns(goto_model.get_symbol_table());

  auto get_goto_function = [this](const irep_idt &id) ->
    const goto_functionst::goto_functiont &
  {
    return goto_model.get_goto_function(id);
  };

  // perform symbolic execution
  symex.resume_symex_from_saved_state(
    get_goto_function, resume.state, &resume.equation, symex_symbol_table);

  // add a partial ordering, if required
  if(resume.equation.has_threads())
  {
    std::unique_ptr<memory_model_baset> memory_model =
      get_memory_model(options, ns);
    memory_model->set_message_handler(ui_message_handler);
    (*memory_model)(resume.equation);
  }

  log.statistics() << "size of program expression: "
               << resume.equation.SSA_steps.size()
               << " steps" << messaget::eom;

  slice(symex, resume.equation, ns, options, ui_message_handler);
}

goto_tracet pathwise_symex_checkert::build_error_trace() const
{
  // currently unsupported
  UNREACHABLE;
}
