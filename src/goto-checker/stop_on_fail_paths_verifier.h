/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property,
        using path-based symbolic execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property,
/// using path-based symbolic execution

#ifndef CPROVER_GOTO_CHECKER_STOP_ON_FAIL_PATHS_VERIFIER_H
#define CPROVER_GOTO_CHECKER_STOP_ON_FAIL_PATHS_VERIFIER_H

#include "goto_verifier.h"
#include "paths_checker.h"

class stop_on_fail_paths_verifiert : public goto_verifiert
{
public:
  stop_on_fail_paths_verifiert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  resultt operator()() override;

  void report() override;

protected:
  abstract_goto_modelt &goto_model;
  paths_checkert goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_STOP_ON_FAIL_PATHS_VERIFIER_H
