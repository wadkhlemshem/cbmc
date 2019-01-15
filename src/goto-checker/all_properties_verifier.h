/*******************************************************************\

Module: Goto Verifier for Verifying all Properties

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Verifying all Properties

#ifndef CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_H
#define CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_H

#include "goto_verifier.h"

#include "bmc_util.h"
#include "incremental_goto_checker.h"
#include "properties.h"
#include "report_util.h"

template <class incremental_goto_checkerT>
class all_properties_verifiert : public goto_verifiert
{
public:
  all_properties_verifiert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model)
    : goto_verifiert(options, ui_message_handler),
      goto_model(goto_model),
      incremental_goto_checker(options, ui_message_handler, goto_model)
  {
    properties = initialize_properties(goto_model);
  }

  resultt operator()() override
  {
    const bool show_trace = options.get_bool_option("trace");

    while(incremental_goto_checker(properties) !=
          incremental_goto_checkert::resultt::DONE)
    {
      // output trace for failed property
      if(show_trace)
      {
        const trace_optionst trace_options(options);
        output_error_trace(
          incremental_goto_checker.build_error_trace(),
          incremental_goto_checker.get_namespace(),
          trace_options,
          ui_message_handler);
      }
      ++iterations;
    }
    return determine_result(properties);
  }

  void report() override
  {
    output_properties(properties, iterations, ui_message_handler);
    output_overall_result(determine_result(properties), ui_message_handler);
  }

protected:
  abstract_goto_modelt &goto_model;
  incremental_goto_checkerT incremental_goto_checker;
  unsigned iterations = 1;
};

#endif // CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_H
