/*******************************************************************\

Module: Cover Goals Reporting Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Cover Goals Reporting Utilities

#ifndef CPROVER_GOTO_CHECKER_COVER_GOALS_REPORT_UTIL_H
#define CPROVER_GOTO_CHECKER_COVER_GOALS_REPORT_UTIL_H

#include "properties.h"

class ui_message_handlert;

void output_goals(
  const propertiest &properties,
  unsigned iterations,
  ui_message_handlert &ui_message_handler);

#endif // CPROVER_GOTO_CHECKER_COVER_GOALS_REPORT_UTIL_H
