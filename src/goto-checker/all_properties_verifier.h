/*******************************************************************\

Module: Goto Verifier for Verifying all Properties

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Verifying all Properties

#ifndef CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_H
#define CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_H

#include "goto_verifier.h"

template<goto_checkerT>
class all_properties_verifiert : public goto_verifiert
{
public:
  all_properties_verifiert(
    const optionst &,
    ui_message_handlert &,
    abstract_goto_modelt &);

  resultt operator()() override;

protected:
  abstract_goto_modelt &goto_model;
  goto_checkerT goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_H
