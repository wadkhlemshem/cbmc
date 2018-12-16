/*******************************************************************\

Module: Goto Checker using Pathwise Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Pathwise Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_PATHWISE_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_PATHWISE_SYMEX_CHECKER_H

#include "goto_checker.h"

#include <goto-symex/path_storage.h>

class symex_bmct;

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
  std::unique_ptr<path_storaget> worklist;

  void perform_symex(symex_bmct &, path_storaget::patht &, symbol_tablet &);
};

#endif // CPROVER_GOTO_CHECKER_PATHWISE_SYMEX_CHECKER_H
