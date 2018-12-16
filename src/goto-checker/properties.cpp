/*******************************************************************\

Module: Properties

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Properties

#include "properties.h"

#include <util/invariant.h>
#include <util/json.h>
#include <util/xml.h>

std::string as_string(resultt result)
{
  switch(result)
  {
  case resultt::UNKNOWN:
    return "UNKNOWN";
  case resultt::PASS:
    return "PASS";
  case resultt::FAIL:
    return "FAIL";
  case resultt::ERROR:
    return "ERROR";
  }

  UNREACHABLE;
}

std::string as_string(property_resultt result)
{
  switch(result)
  {
  case property_resultt::NOT_REACHED:
    return "NOT REACHED";
  case property_resultt::UNKNOWN:
    return "UNKNOWN";
  case property_resultt::NOT_REACHABLE:
    return "UNREACHABLE";
  case property_resultt::PASS:
    return "PASS";
  case property_resultt::FAIL:
    return "FAIL";
  case property_resultt::ERROR:
    return "ERROR";
  }

  UNREACHABLE;
}

/// Returns the properties in the goto model
propertiest initialize_properties(const abstract_goto_modelt &goto_model)
{
  propertiest properties;
  forall_goto_functions(it, goto_model.get_goto_functions())
  {
    if(
      !it->second.is_inlined() ||
      it->first == goto_functionst::entry_point())
    {
      const goto_programt &goto_program = it->second.body;

      forall_goto_program_instructions(i_it, goto_program)
      {
        if(!i_it->is_assert())
          continue;

        const source_locationt &source_location = i_it->source_location;

        irep_idt property_id = source_location.get_property_id();

        property_infot &property = properties[property_id];
        property.result = property_resultt::NOT_REACHED;
        property.location = i_it;
      }
    }
  }
  return properties;
}

std::string
as_string(const irep_idt &property_id, const property_infot &property_info)
{
  return "[" + id2string(property_id) + "] " + property_info.description +
         ": " + as_string(property_info.result);
}

xmlt xml(const irep_idt &property_id, const property_infot &property_info)
{
  xmlt xml_result("result");
  xml_result.set_attribute("property", id2string(property_id));
  xml_result.set_attribute("status", as_string(property_info.result));
  return xml_result;
}

json_objectt
json(const irep_idt &property_id, const property_infot &property_info)
{
  json_objectt result;
  result["property"] = json_stringt(property_id);
  result["description"] = json_stringt(property_info.description);
  result["status"] = json_stringt(as_string(property_info.result));
  return result;
}
