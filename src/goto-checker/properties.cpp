/*******************************************************************\

Module: Properties

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Properties

#include "properties.h"

#include <util/exit_codes.h>
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

/// Update with the preference order
/// 1. old non-UNKNOWN/non-NOT_REACHED result
/// 2. new non-UNKNOWN/non-NOT_REACHED result
/// 3. UNKNOWN
/// 4. NOT_REACHED
/// Suitable for updating property results
property_resultt &operator|=(property_resultt &a, property_resultt const &b)
{
  // non-monotonic use is likely a bug
  PRECONDITION(
    a == property_resultt::NOT_REACHED ||
    (a == property_resultt::UNKNOWN && b != property_resultt::NOT_REACHED) ||
    a == b);
  switch(a)
  {
  case property_resultt::NOT_REACHED:
  case property_resultt::UNKNOWN:
    a = b;
    return a;
  case property_resultt::ERROR:
  case property_resultt::PASS:
  case property_resultt::FAIL:
    return a;
  }
  UNREACHABLE;
}

/// Update with the preference order
/// 1. ERROR
/// 2. FAIL
/// 3. UNKNOWN
/// 4. NOT_REACHED
/// 5. PASS
/// Suitable for computing overall results
property_resultt &operator&=(property_resultt &a, property_resultt const &b)
{
  switch(a)
  {
  case property_resultt::ERROR:
    a = b;
    return a;
  case property_resultt::FAIL:
    a = (b == property_resultt::ERROR ? b : a);
    return a;
  case property_resultt::UNKNOWN:
    a = (b == property_resultt::ERROR || b == property_resultt::FAIL ? b : a);
    return a;
  case property_resultt::NOT_REACHED:
    a = (b != property_resultt::PASS ? b : a);
    return a;
  case property_resultt::PASS:
    a = (b == property_resultt::PASS ? a : b);
    return a;
  }
  UNREACHABLE;
}

/// Determines the overall result corresponding from the given properties
/// That is PASS if all properties are PASS or NOT_REACHED,
///         FAIL if at least one property is FAIL and no property is ERROR,
///         UNKNOWN if no property is FAIL or ERROR and
///           at least one property is UNKNOWN,
///         ERROR if at least one property is error.
resultt determine_result(const propertiest &properties)
{
  property_resultt result = property_resultt::PASS;
  for(const auto &property_pair : properties)
  {
    result &= property_pair.second.result;
  }
  // If we haven't reached anything then overall it's still a PASS.
  if(result == property_resultt::NOT_REACHED)
    result = property_resultt::PASS;
  return static_cast<resultt>(result);
}

/// Returns true if there as a property with NOT_REACHED or UNKNOWN result.
bool has_properties_to_check(const propertiest &properties)
{
  for(const auto &property_pair : properties)
  {
    if(
      property_pair.second.result == property_resultt::NOT_REACHED ||
      property_pair.second.result == property_resultt::UNKNOWN)
    {
      return true;
    }
  }
  return false;
}

std::size_t
count_properties(const propertiest &properties, property_resultt result)
{
  std::size_t count = 0;
  for(const auto &property_pair : properties)
  {
    if(property_pair.second.result == result)
      ++count;
  }
  return count;
}

/// Merges a set of properties into a given set of properties,
/// updating its results and adding new properties.
propertiest &operator|=(
  propertiest &properties, const propertiest &updated_properties)
{
  for(const auto &property_pair : updated_properties)
  {
    auto found_property = properties.insert(property_pair);
    if(!found_property.second)
      found_property.first->second.result |= property_pair.second.result;
  }
  return properties;
}

int result_to_exit_code(resultt result)
{
  switch(result)
  {
    case resultt::PASS:
      return CPROVER_EXIT_VERIFICATION_SAFE;
    case resultt::FAIL:
      return CPROVER_EXIT_VERIFICATION_UNSAFE;
    case resultt::ERROR:
      return CPROVER_EXIT_INTERNAL_ERROR;
    case resultt::UNKNOWN:
      return CPROVER_EXIT_VERIFICATION_INCONCLUSIVE;
  }
}
