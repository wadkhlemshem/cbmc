/*******************************************************************\

Module: Goto Verifier for Verifying all Properties with BMC

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Verifying all Properties with BMC

#ifndef CPROVER_GOTO_CHECKER_ALL_PROPERTIES_PATHS_VERIFIER_H
#define CPROVER_GOTO_CHECKER_ALL_PROPERTIES_PATHS_VERIFIER_H

#include "goto_verifier.h"
#include "paths_checker.h"

class all_properties_paths_verifiert : public goto_verifiert
{
public:
  all_properties_paths_verifiert(
    const optionst &,
    ui_message_handlert &,
    abstract_goto_modelt &);

  resultt operator()() override;

protected:
  abstract_goto_modelt &goto_model;
  paths_checkert goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_ALL_PROPERTIES_PATHS_VERIFIER_H
