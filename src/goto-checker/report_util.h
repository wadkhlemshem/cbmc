/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#ifndef CPROVER_GOTO_CHECKER_REPORT_UTIL_H
#define CPROVER_GOTO_CHECKER_REPORT_UTIL_H

#include "properties.h"

class goto_tracet;
struct trace_optionst;
class ui_message_handlert;

void report_success(ui_message_handlert &);
void report_failure(ui_message_handlert &);
void report_inconclusive(ui_message_handlert &);
void report_error(ui_message_handlert &);

void output_properties(
  const propertiest &properties,
  unsigned iterations,
  ui_message_handlert &ui_message_handler);

void output_properties_with_traces(
  const propertiest &properties,
  const std::unordered_map<irep_idt, std::vector<goto_tracet>::const_iterator>
    &property_traces,
  const namespacet &ns,
  const trace_optionst &trace_options,
  unsigned iterations,
  ui_message_handlert &ui_message_handler);

void output_overall_result(
  resultt result,
  ui_message_handlert &ui_message_handler);

#endif // CPROVER_GOTO_CHECKER_REPORT_UTIL_H
