/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property,
        using path-based symbolic execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property,
/// using path-based symbolic execution

#include "stop_on_fail_paths_verifier.h"

stop_on_fail_paths_verifiert::stop_on_fail_paths_verifiert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_verifiert(options, ui_message_handler),
    goto_model(goto_model),
    goto_checker(options, ui_message_handler, goto_model)
{
}

resultt stop_on_fail_paths_verifiert::operator()()
{
  return resultt::UNKNOWN;
}
