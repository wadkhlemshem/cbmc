/*******************************************************************\

Module: Goto Verifier Interface

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier Interface

#include "goto_verifier.h"

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
      log.result() << "\n** Results:" << messaget::eom;

      // collect properties in a vector
      std::vector<propertiest::const_iterator> sorted_properties;

      for(auto p_it = properties.begin(); p_it != properties.end(); p_it++)
        sorted_properties.push_back(p_it);

      // now determine an ordering for those goals:
      // 1. alphabetical ordering of file name
      // 2. numerical ordering of line number
      // 3. alphabetical ordering of goal ID
      std::sort(
        sorted_properties.begin(),
        sorted_properties.end(),
        [](propertiest::const_iterator pit1, propertiest::const_iterator pit2) {
          const auto &p1 = pit1->second.location->source_location;
          const auto &p2 = pit2->second.location->source_location;
          if(p1.get_file() != p2.get_file())
            return id2string(p1.get_file()) < id2string(p2.get_file());
          else if(!p1.get_line().empty() && !p2.get_line().empty())
            return std::stoul(id2string(p1.get_line())) <
                   std::stoul(id2string(p2.get_line()));
          else
            return id2string(pit1->first) < id2string(pit2->first);
        });

      // now show in the order we have determined

      irep_idt previous_function;
      irep_idt current_file;
      for(const auto &p : sorted_properties)
      {
        const auto &l = p->second.location->source_location;

        if(l.get_function() != previous_function)
        {
          if(!previous_function.empty())
            log.result() << '\n';
          previous_function = l.get_function();
          if(!previous_function.empty())
          {
            current_file = l.get_file();
            if(!current_file.empty())
              log.result() << current_file << ' ';
            if(!l.get_function().empty())
              log.result() << "function " << l.get_function();
            log.result() << messaget::eom;
          }
        }

        log.result() << messaget::faint << '[' << p->first << "] " << messaget::reset;

        if(l.get_file() != current_file)
          log.result() << "file " << l.get_file() << ' ';

        if(!l.get_line().empty())
          log.result() << "line " << l.get_line() << ' ';

        log.result() << p->second.description << ": ";

        switch(p->second.result)
        {
          case property_resultt::NOT_REACHED:
            log.result() << messaget::magenta;
            break;
          case property_resultt::UNKNOWN:
            log.result() << messaget::bright_magenta;
            break;
          case property_resultt::NOT_REACHABLE:
            log.result() << messaget::bright_green;
            break;
          case property_resultt::PASS:
            log.result() << messaget::green;
            break;
          case property_resultt::FAIL:
            log.result() << messaget::red;
            break;
          case property_resultt::ERROR:
            log.result() << messaget::bright_red;
            break;
        }

        log.result() << as_string(p->second.result) << messaget::reset << messaget::eom;
      }

      log.status() << "\n** " << count_properties(properties, property_resultt::FAIL)
               << " of " << properties.size() << " failed" << messaget::eom;
      break;
    }
    case ui_message_handlert::uit::XML_UI:
    {
      for(const auto &property_pair : properties)
      {
        log.result() << xml(property_pair.first, property_pair.second);
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
