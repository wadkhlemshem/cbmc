/*******************************************************************\

Module: Goto Verifier for stopping at the first failing property,
        using BMC, with fault localization

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for stopping at the first failing property, using BMC,
/// with fault localization

#ifndef CPROVER_GOTO_CHECKER_STOP_ON_FAIL_BMC_VERIFIER_FAULT_LOCALIZATION_H
#define CPROVER_GOTO_CHECKER_STOP_ON_FAIL_BMC_VERIFIER_FAULT_LOCALIZATION_H

#include "bmc_checker.h"
#include "goto_verifier.h"

class stop_on_fail_bmc_verifier_fault_localizationt : public goto_verifiert
{
public:
  stop_on_fail_bmc_verifier_fault_localizationt(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  resultt operator()() override;

  void report() override;

protected:
  abstract_goto_modelt &goto_model;
  bmc_checkert goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_STOP_ON_FAIL_BMC_VERIFIER_FAULT_LOCALIZATION_H
