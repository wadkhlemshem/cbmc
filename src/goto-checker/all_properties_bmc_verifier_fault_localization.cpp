/*******************************************************************\

Module: Goto Verifier for Verifying all Properties with BMC

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Verifying all Properties with BMC and fault localization

#include "all_properties_bmc_verifier_fault_localization.h"

all_properties_bmc_verifier_fault_localizationt::all_properties_bmc_verifier_fault_localizationt(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_verifiert(options, ui_message_handler),
    goto_model(goto_model),
    goto_checker(options, ui_message_handler, goto_model)
{
}

resultt all_properties_bmc_verifier_fault_localizationt::operator()()
{
  return resultt::UNKNOWN;
}

void all_properties_bmc_verifier_fault_localizationt::report()
{

}
