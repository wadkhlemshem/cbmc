/*******************************************************************\

Module: Goto Verifier for Verifying all Properties with BMC

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Verifying all Properties with BMC and fault localization

#ifndef CPROVER_GOTO_CHECKER_ALL_PROPERTIES_BMC_VERIFIER_FAULT_LOCALIZATION_H
#define CPROVER_GOTO_CHECKER_ALL_PROPERTIES_BMC_VERIFIER_FAULT_LOCALIZATION_H

#include "bmc_checker.h"
#include "goto_verifier.h"

class all_properties_bmc_verifier_fault_localizationt : public goto_verifiert
{
public:
  all_properties_bmc_verifier_fault_localizationt(
    const optionst &,
    ui_message_handlert &,
    abstract_goto_modelt &);

  resultt operator()() override;

  void report() override;

protected:
  abstract_goto_modelt &goto_model;
  bmc_checkert goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_ALL_PROPERTIES_BMC_VERIFIER_FAULT_LOCALIZATION_H
