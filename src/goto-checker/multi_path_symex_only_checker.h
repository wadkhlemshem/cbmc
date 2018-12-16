/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution only

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution only (no SAT solving)

#ifndef CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_ONLY_CHECKER_H
#define CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_ONLY_CHECKER_H

#include "incremental_goto_checker.h"

#include "symex_bmc.h"

class multi_path_symex_only_checkert : public incremental_goto_checkert
{
public:
  multi_path_symex_only_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  resultt operator()(propertiest &) override;

  goto_tracet build_error_trace() const override;

  void output_error_witness(const goto_tracet &) override;
  void output_proof() override;

protected:
  abstract_goto_modelt &goto_model;
  symbol_tablet symex_symbol_table;
  symex_target_equationt equation;
  path_fifot path_storage; // should go away
  symex_bmct symex;

  void perform_symex();
};

#endif // CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_ONLY_CHECKER_H
