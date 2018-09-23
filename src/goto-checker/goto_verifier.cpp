/*******************************************************************\

Module: Goto Verifier Interface

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier Interface

#include "goto_verifier.h"

#include <util/json_stream.h>
#include <util/xml.h>

#include "bmc_util.h"
#include "properties.h"

goto_verifiert::goto_verifiert(
  const optionst &_options,
  ui_message_handlert &ui_message_handler)
  : options(_options),
    ui_message_handler(ui_message_handler),
    log(ui_message_handler)
{
}

void goto_verifiert::report()
{
  switch(ui_message_handler.get_ui())
  {
    case ui_message_handlert::uit::PLAIN:
    {
      result() << "\n** Results:" << eom;

      for(const auto &property_pair : properties)
      {
        result() << as_string(property_pair.first, property_pair.second)
                 << eom;
      }

      status() << "\n** " << count_properties(properties, resultt::FAIL)
               << " of " << properties.size() << " failed" << eom;
      break;
    }
    case ui_message_handlert::uit::XML_UI:
    {
      for(const auto &property_pair : properties)
      {
        result() << xml(property_pair.first, property_pair.second);
      }
      break;
    }
    case ui_message_handlert::uit::JSON_UI:
    {
      json_stream_objectt &json_result =
        ui_message_handler.get_json_stream().push_back_stream_object();
      json_stream_arrayt &result_array =
        json_result.push_back_stream_array("result");

      for(const auto &property_pair : properties)
      {
        result_array.push_back(
          json(property_pair.first, property_pair.second));
      }
      break;
    }
  }

  switch(determine_result(properties))
  {
    case resultt::PASS:
      report_success(ui_message_handler);
      break;
    case resultt::FAIL:
      report_failure(ui_message_handler);
      break;
    case resultt::UNKNOWN:
      report_inconclusive(ui_message_handler);
      break;
    case resultt::ERROR:
      report_error(ui_message_handler);
      break;
  }
}
