/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H

#include "goto_checker.h"

class multi_path_symex_checkert : public goto_checkert
{
public:
  multi_path_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  propertiest operator()(const propertiest &) override;

  goto_tracet build_error_trace() const override;

protected:
  abstract_goto_modelt &goto_model;
};

#endif // CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H
