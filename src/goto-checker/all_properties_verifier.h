/*******************************************************************\

Module: Goto Verifier for Verifying all Properties

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Verifying all Properties

#ifndef CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_H
#define CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_H

#include "goto_verifier.h"

template<class goto_checkerT>
class all_properties_verifiert : public goto_verifiert
{
public:
  all_properties_verifiert(
    const optionst &,
    ui_message_handlert &,
    abstract_goto_modelt &)
  : goto_verifiert(options, ui_message_handler),
    goto_model(goto_model),
    goto_checker(options, ui_message_handler, goto_model),
    properties(initialize_properties(goto_model))
  {
  }

  resultt operator()() override
  {
    // have we got anything to check? otherwise we return PASS
    if(!has_properties_to_check(properties))
      return resultt::PASS;

    while(goto_checker(properties) != goto_checkert::statust::DONE)
    {
      // loop until we are done
    }
    return determine_result(properties);
  }

protected:
  abstract_goto_modelt &goto_model;
  goto_checkerT goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_H
