/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#include "bmc_util.h"

#include <goto-symex/memory_model_pso.h>
#include <goto-symex/symex_target_equation.h>

#include <solvers/prop/prop_conv.h>

#include <util/make_unique.h>
#include <util/ui_message.h>


void error_trace()
{
  status() << "Building error trace" << eom;

  goto_tracet &goto_trace=safety_checkert::error_trace;
  build_goto_trace(equation, prop_conv, ns, goto_trace);

  switch(ui)
  {
    case ui_message_handlert::uit::PLAIN:
      result() << "Counterexample:" << eom;
      show_goto_trace(result(), ns, goto_trace, trace_options());
      result() << eom;
      break;

    case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml;
      convert(ns, goto_trace, xml);
      status() << xml;
    }
      break;

    case ui_message_handlert::uit::JSON_UI:
    {
      json_stream_objectt &json_result =
        status().json_stream().push_back_stream_object();
      const goto_trace_stept &step=goto_trace.steps.back();
      json_result["property"] =
        json_stringt(step.pc->source_location.get_property_id());
      json_result["description"] =
        json_stringt(step.pc->source_location.get_comment());
      json_result["status"]=json_stringt("failed");
      json_stream_arrayt &json_trace =
        json_result.push_back_stream_array("trace");
      convert<json_stream_arrayt>(ns, goto_trace, json_trace, trace_options());
    }
      break;
  }
}

/// outputs witnesses in graphml format
void output_graphml(resultt result)
{
  const std::string graphml=options.get_option("graphml-witness");
  if(graphml.empty())
    return;

  graphml_witnesst graphml_witness(ns);
  if(result==resultt::UNSAFE)
    graphml_witness(safety_checkert::error_trace);
  else if(result==resultt::SAFE)
    graphml_witness(equation);
  else
    return;

  if(graphml=="-")
    write_graphml(graphml_witness.graph(), std::cout);
  else
  {
    std::ofstream out(graphml);
    write_graphml(graphml_witness.graph(), out);
  }
}

void convert_symex_target_equation(
  symex_target_equationt &equation,
  prop_convt &prop_conv,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  msg.status() << "converting SSA" << messaget::eom;

  // convert SSA
  equation.convert(prop_conv);
}

std::unique_ptr<memory_modelt> get_memory_model(
  const optionst &options,
  const namespacet &ns)
{
  const std::string mm=options.get_option("mm");

  if(mm.empty() || mm=="sc")
    return util_make_unique<memory_model_sct>(ns);
  else if(mm=="tso")
    return util_make_unique<memory_model_tsot>(ns);
  else if(mm=="pso")
    return util_make_unique<memory_model_psot>(ns);
  else
  {
    throw "invalid memory model '" + mm + "': use one of sc, tso, pso";
  }
}

void setup_symex()
{
  get_memory_model();

  {
    const symbolt *init_symbol;
    if(!ns.lookup(INITIALIZE_FUNCTION, init_symbol))
      symex.language_mode=init_symbol->mode;
  }

  status() << "Starting Bounded Model Checking" << eom;

  symex.last_source_location.make_nil();

  symex.unwindset.parse_unwind(options.get_option("unwind"));
  symex.unwindset.parse_unwindset(options.get_option("unwindset"));
}

void slice()
{
  if(options.get_option("slice-by-trace")!="")
  {
    symex_slice_by_tracet symex_slice_by_trace(ns);

    symex_slice_by_trace.slice_by_trace
      (options.get_option("slice-by-trace"),
       equation);
  }
  // any properties to check at all?
  if(equation.has_threads())
  {
    // we should build a thread-aware SSA slicer
    statistics() << "no slicing due to threads" << eom;
  }
  else
  {
    if(options.get_bool_option("slice-formula"))
    {
      ::slice(equation);
      statistics() << "slicing removed "
                   << equation.count_ignored_SSA_steps()
                   << " assignments"<<eom;
    }
    else
    {
      if(options.get_list_option("cover").empty())
      {
        simple_slice(equation);
        statistics() << "simple slicing removed "
                     << equation.count_ignored_SSA_steps()
                     << " assignments"<<eom;
      }
    }
  }
  statistics() << "Generated "
               << symex.total_vccs<<" VCC(s), "
               << symex.remaining_vccs
               << " remaining after simplification" << eom;
}

void report_success(ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  msg.result() << "VERIFICATION SUCCESSFUL" << messaget::eom;

  switch(ui_message_handler.get_ui())
  {
    case ui_message_handlert::uit::PLAIN:
      break;

    case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      msg.result() << xml;
    }
      break;

    case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_result;
      json_result["cProverStatus"]=json_stringt("success");
      msg.result() << json_result;
    }
      break;
  }
}

void report_failure(ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  msg.result() << "VERIFICATION FAILED" << messaget::eom;

  switch(ui_message_handler.get_ui())
  {
    case ui_message_handlert::uit::PLAIN:
      break;

    case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      msg.result() << xml;
    }
      break;

    case ui_message_handlert::uit::JSON_UI:
    {
      json_objectt json_result;
      json_result["cProverStatus"] = json_stringt("failure");
      msg.result() << json_result;
    }
      break;
  }
}
