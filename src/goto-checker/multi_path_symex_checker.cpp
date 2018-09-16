/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution

#include "multi_path_symex_checker.h"

multi_path_symex_checkert::multi_path_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_checkert(options, ui_message_handler),
    goto_model(goto_model)
{
}

propertiest multi_path_symex_checkert::operator()(const propertiest &properties)
{
  return properties;
}

goto_tracet multi_path_symex_checkert::build_error_trace() const
{
  goto_tracet goto_trace;
  return goto_trace;
}