/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking

#ifndef CPROVER_GOTO_CHECKER_BMC_CHECKER_H
#define CPROVER_GOTO_CHECKER_BMC_CHECKER_H

#include "multi_path_symex_checker.h"

class bmc_checkert : public multi_path_symex_checkert
{
public:
  bmc_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  statust operator()(propertiest &) override;

  goto_tracet build_error_trace() const override;
  void output_error_witness(const goto_tracet &) override;
  void output_proof() override;
};

#endif // CPROVER_GOTO_CHECKER_BMC_CHECKER_H
