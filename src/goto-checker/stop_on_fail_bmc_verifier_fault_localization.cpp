/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property,
        using BMC, with fault localization

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property, using BMC,
/// with fault localization

#include "stop_on_fail_bmc_verifier_fault_localization.h"

stop_on_fail_bmc_verifier_fault_localizationt::stop_on_fail_bmc_verifier_fault_localizationt(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_verifiert(options, ui_message_handler),
    goto_model(goto_model),
    goto_checker(options, ui_message_handler, goto_model)
{
}

resultt stop_on_fail_bmc_verifier_fault_localizationt::operator()()
{
  return resultt::UNKNOWN;
}

void stop_on_fail_bmc_verifier_fault_localizationt::report()
{

}
