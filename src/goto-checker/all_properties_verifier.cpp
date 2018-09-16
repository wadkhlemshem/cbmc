/*******************************************************************\

Module: Goto Verifier for Verifying all Properties

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Verifying all Properties

#include "all_properties_verifier.h"

all_properties_verifiert::all_properties_verifiert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_verifiert(options, ui_message_handler),
    goto_model(goto_model),
    goto_checker(options, ui_message_handler, goto_model)
{
}

resultt all_properties_verifiert::operator()()
{
  return resultt::UNKNOWN;
}
