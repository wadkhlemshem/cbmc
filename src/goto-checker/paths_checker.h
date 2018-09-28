/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Path-Based Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_PATHS_CHECKER_H
#define CPROVER_GOTO_CHECKER_PATHS_CHECKER_H

#include "pathwise_symex_checker.h"

#include "solver_factory.h"

class paths_checkert : public pathwise_symex_checkert
{
public:
  paths_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  statust operator()(propertiest &) override;

  goto_tracet build_error_trace() const override;

  void output_error_witness(const goto_tracet &) override;

  void output_proof() override
  {
    // unsupported
    UNIMPLEMENTED;
  }

protected:
  std::unique_ptr<solver_factoryt::solvert> solver;
};

#endif // CPROVER_GOTO_CHECKER_PATHS_CHECKER_H
