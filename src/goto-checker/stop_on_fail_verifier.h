/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property

#ifndef CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_H
#define CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_H

#include "goto_verifier.h"

template<class goto_checkerT>
class stop_on_fail_verifiert : public goto_verifiert
{
public:
  stop_on_fail_verifiert(
    const optionst &,
    ui_message_handlert &,
    abstract_goto_modelt &)
  : goto_verifiert(options, ui_message_handler),
    goto_model(goto_model),
    goto_checker(options, ui_message_handler, goto_model)
  {
    properties = std::move(initialize_properties(goto_model));
  }

  resultt operator()() override
  {
    // have we got anything to check? otherwise we return PASS
    if(!has_properties_to_check(properties))
      return resultt::PASS;

    (void)goto_checker(properties);
    return determine_result(properties);
  }

  void report() override;

protected:
  abstract_goto_modelt &goto_model;
  goto_checkerT goto_checker;
};

template<class goto_checkerT>
void stop_on_fail_verifiert::report()
{
  switch(determine_result(properties))
  {
    case resultt::PASS:
      report_success(ui_message_handler);
      goto_checker.output_proof();
      break;

    case resultt::FAIL:
    {
      goto_tracet error_trace = goto_checker.build_error_trace();
      output_error_trace(error_trace, ns, trace_options(), ui_message_handler);
      report_failure(ui_message_handler);
      goto_checker.output_error_witness(error_trace);
      break;
    }

    case resultt::UNKNOWN:
      report_inconclusive(ui_message_handler);
      break;

    case resultt::ERROR:
      report_error(ui_message_handler);
      break;
  }
}

#endif // CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_H
