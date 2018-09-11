/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Path-Based Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_PATHS_CHECKER_H
#define CPROVER_GOTO_CHECKER_PATHS_CHECKER_H

#include "goto_checker.h"

class paths_checkert : public goto_checkert
{
public:
  paths_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  propertiest operator()(const propertiest &) override;

  goto_tracet build_error_trace() const override;

protected:
  abstract_goto_modelt &goto_model;
};

#endif // CPROVER_GOTO_CHECKER_PATHS_CHECKER_H
