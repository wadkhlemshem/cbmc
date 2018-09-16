/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property

#ifndef CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_H
#define CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_H

#include "goto_verifier.h"

template<goto_checkerT>
class stop_on_fail_verifiert : public goto_verifiert
{
public:
  stop_on_fail_verifiert(
    const optionst &,
    ui_message_handlert &,
    abstract_goto_modelt &);

  resultt operator()() override;

protected:
  abstract_goto_modelt &goto_model;
  goto_checkerT goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_STOP_ON_FAIL_VERIFIER_H
