/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property

#include "stop_on_fail_verifier.h"

stop_on_fail_verifiert::stop_on_fail_verifiert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_verifiert(options, ui_message_handler),
    goto_model(goto_model),
    goto_checker(options, ui_message_handler, goto_model)
{
}

resultt stop_on_fail_verifiert::operator()()
{
  return resultt::UNKNOWN;
}
