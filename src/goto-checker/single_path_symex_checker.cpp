/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Path-Based Symbolic Execution

#include "paths_checker.h"

paths_checkert::paths_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_checkert(options, ui_message_handler),
    goto_model(goto_model)
{
}

propertiest paths_checkert::operator()(const propertiest &properties)
{
  return properties;
}

goto_tracet paths_checkert::build_error_trace() const
{
  goto_tracet goto_trace;
  return goto_trace;
}