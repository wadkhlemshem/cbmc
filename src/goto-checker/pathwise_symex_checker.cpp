/*******************************************************************\

Module: Goto Checker using Pathwise Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Pathwise Symbolic Execution

#include "pathwise_symex_checker.h"

#include <util/invariant.h>

pathwise_symex_checkert::pathwise_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : goto_checkert(options, ui_message_handler),
    goto_model(goto_model)
{
}

propertiest pathwise_symex_checkert::operator()(const propertiest &properties)
{
  return properties;
}

goto_tracet pathwise_symex_checkert::build_error_trace() const
{
  // currently unsupported
  UNREACHABLE;
}
