/*******************************************************************\

Module: Goto Verifier for Verifying all Properties that stores Traces

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto verifier for verifying all properties that stores traces

#ifndef CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_WITH_TRACE_STORAGE_H
#define CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_WITH_TRACE_STORAGE_H

#include "goto_verifier.h"

#include "incremental_goto_checker.h"
#include "properties.h"
#include "report_util.h"

template <class incremental_goto_checkerT>
class all_properties_verifier_with_trace_storaget : public goto_verifiert
{
public:
  all_properties_verifier_with_trace_storaget(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model)
    : goto_verifiert(options, ui_message_handler),
      goto_model(goto_model),
      incremental_goto_checker(options, ui_message_handler, goto_model)
  {
    properties = initialize_properties(goto_model);
  }

  resultt operator()() override
  {
    // have we got anything to check? otherwise we return PASS
    if(!has_properties_to_check(properties))
      return resultt::PASS;

    while(incremental_goto_checker(properties) !=
          incremental_goto_checkert::resultt::DONE)
    {
      // we've got an error trace; store it and link it to the failed properties
      error_traces.push_back(incremental_goto_checker.build_error_trace());
      for(const auto &property_pair : properties)
      {
        if(property_pair.second.status == property_statust::FAIL)
        {
          // only link trace to new FAILures
          property_traces.emplace(
            property_pair.first, std::prev(error_traces.end()));
        }
      }
    }
    return determine_result(properties);
  }

  void report() override
  {
    if(options.get_bool_option("trace"))
    {
      const namespacet ns(goto_model.get_symbol_table());
      const trace_optionst trace_options(options);
      output_properties_with_traces(
        properties, property_traces, ns, trace_options, ui_message_handler);
    }
    else
    {
      output_properties(properties, ui_message_handler);
    }
    output_overall_result(determine_result(properties), ui_message_handler);
  }

  const std::vector<goto_tracet> &get_error_traces() const
  {
    return error_traces;
  }

  const goto_tracet &get_error_trace(const irep_idt &property_id) const
  {
    return *property_traces.at(property_id);
  }

protected:
  abstract_goto_modelt &goto_model;
  incremental_goto_checkerT incremental_goto_checker;

  /// stores the traces
  std::vector<goto_tracet> error_traces;

  // maps property IDs to traces
  std::unordered_map<irep_idt, std::vector<goto_tracet>::const_iterator>
    property_traces;
};

#endif // CPROVER_GOTO_CHECKER_ALL_PROPERTIES_VERIFIER_WITH_TRACE_STORAGE_H
