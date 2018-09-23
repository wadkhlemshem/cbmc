/*******************************************************************\

Module: Goto Checker using Pathwise Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Pathwise Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_PATHWISE_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_PATHWISE_SYMEX_CHECKER_H

#include "goto_checker.h"

class pathwise_symex_checkert : public goto_checkert
{
public:
  pathwise_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  statust operator()(propertiest &) override;

  goto_tracet build_error_trace() const override;

  void output_error_witness(const goto_tracet &) override
  {
    // unsupported
    UNIMPLEMENTED;
  }
  void output_proof() override
  {
    // unsupported
    UNIMPLEMENTED;
  }

protected:
  abstract_goto_modelt &goto_model;
};

#endif // CPROVER_GOTO_CHECKER_PATHWISE_SYMEX_CHECKER_H
