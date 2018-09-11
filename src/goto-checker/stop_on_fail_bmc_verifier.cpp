/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property,
        using BMC

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property, using BMC

#include "stop_on_fail_bmc_verifier.h"

stop_on_fail_bmc_verifiert::stop_on_fail_bmc_verifiert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_verifiert(options, ui_message_handler),
    goto_model(goto_model),
    goto_checker(options, ui_message_handler, goto_model)
{
}

resultt stop_on_fail_bmc_verifiert::operator()()
{
  return resultt::UNKNOWN;
}
