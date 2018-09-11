/*******************************************************************\

Module: Goto Verifier for Verifying all Properties with BMC

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Verifying all Properties with BMC

#ifndef CPROVER_GOTO_CHECKER_ALL_PROPERTIES_BMC_VERIFIER_H
#define CPROVER_GOTO_CHECKER_ALL_PROPERTIES_BMC_VERIFIER_H

#include "bmc_checker.h"
#include "goto_verifier.h"

class all_properties_bmc_verifiert : public goto_verifiert
{
public:
  all_properties_bmc_verifiert(
    const optionst &,
    ui_message_handlert &,
    abstract_goto_modelt &);

  resultt operator()() override;

protected:
  abstract_goto_modelt &goto_model;
  bmc_checkert goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_ALL_PROPERTIES_BMC_VERIFIER_H
