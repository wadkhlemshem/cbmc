/*******************************************************************\

Module: Goto Verifier for Verifying all Properties with BMC

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Verifying all Properties with BMC

#ifndef CPROVER_GOTO_CHECKER_ALL_PROPERTIES_BMC_VERIFIER_H
#define CPROVER_GOTO_CHECKER_ALL_PROPERTIES_BMC_VERIFIER_H

#include "goto_verifier.h"

class all_properties_bmc_verifiert : public goto_verifiert
{
public:
  all_properties_bmc_verifiert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  resultt operator()() override;

  void report() override;

protected:
  abstract_goto_modelt &goto_model;
  bmc_checkert goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_ALL_PROPERTIES_BMC_VERIFIER_H
