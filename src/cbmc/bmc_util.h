/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#ifndef CPROVER_CBMC_BMC_UTIL_H
#define CPROVER_CBMC_BMC_UTIL_H

class symex_target_equationt;
class prop_convt;
class message_handlert;
class ui_message_handlert;

void convert_symex_target_equation(
  symex_target_equationt &equation,
  prop_convt &prop_conv,
  message_handlert &message_handler);

void report_failure(ui_message_handlert &message_handler);
void report_success(ui_message_handlert &message_handler);

void output_error_trace();
void output_graphml(resultt result);
void get_memory_model();
void setup_symex();
void slice();

#endif // CPROVER_CBMC_BMC_UTIL_H

