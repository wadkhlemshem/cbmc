/*******************************************************************\

Module: Goto Verifier for Verifying all Properties with BMC

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Verifying all Properties with BMC

#include "all_properties_bmc_verifier.h"

all_properties_bmc_verifiert::all_properties_bmc_verifiert(
  const optionst &_options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_verifiert(options, ui_message_handler),
    goto_model(goto_model)
{
}
