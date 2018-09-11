/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property,
        using BMC

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property, using BMC

#ifndef CPROVER_GOTO_CHECKER_STOP_ON_FAIL_BMC_VERIFIER_H
#define CPROVER_GOTO_CHECKER_STOP_ON_FAIL_BMC_VERIFIER_H

#include "bmc_checker.h"
#include "goto_verifier.h"

class stop_on_fail_bmc_verifiert : public goto_verifiert
{
public:
  stop_on_fail_bmc_verifiert(
    const optionst &,
    ui_message_handlert &,
    abstract_goto_modelt &);

  resultt operator()() override;

protected:
  abstract_goto_modelt &goto_model;
  bmc_checkert goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_STOP_ON_FAIL_BMC_VERIFIER_H
