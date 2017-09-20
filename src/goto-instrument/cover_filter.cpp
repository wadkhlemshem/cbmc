/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Filters for the Coverage Instrumentation

#include "cover_filter.h"

#include <json/json_parser.h>

#include <util/message.h>

/// Filter out functions that are not considered provided by the user
/// \param identifier: a function name
/// \param goto_function: a goto function
/// \return: returns true if function is considered user-provided
bool internal_functions_filtert::operator()(
  const irep_idt &identifier,
  const goto_functionst::goto_functiont &goto_function) const
{
  if(identifier==goto_functionst::entry_point())
    return false;

  if(identifier==(CPROVER_PREFIX "initialize"))
    return false;

  if(goto_function.is_hidden())
    return false;

  // ignore Java array built-ins
  if(has_prefix(id2string(identifier), "java::array"))
    return false;

  // ignore if built-in library
  if(!goto_function.body.instructions.empty() &&
     goto_function.body.instructions.front().source_location.is_built_in())
    return false;

  return true;
}

/// Filter functions whose name match the regex
/// \param identifier: a function name
/// \param goto_function: a goto function
/// \return: returns true if the function name matches
bool include_pattern_filtert::operator()(
  const irep_idt &identifier,
  const goto_functionst::goto_functiont &goto_function) const
{
  std::smatch string_matcher;
  return std::regex_match(
    id2string(identifier), string_matcher, regex_matcher);
}

/// Call a goto_program non-trivial if it has:
///  * Any declarations
///  * At least 2 branches
///  * At least 5 assignments
/// \param identifier: a function name
/// \param goto_function: a goto function
/// \return: returns true if non-trivial
bool trivial_functions_filtert::operator()(
  const irep_idt &identifier,
  const goto_functionst::goto_functiont &goto_function) const
{
  unsigned long count_assignments=0, count_goto=0;
  forall_goto_program_instructions(i_it, goto_function.body)
  {
    if(i_it->is_goto())
    {
      if((++count_goto)>=2)
        return true;
    }
    else if(i_it->is_assign())
    {
      if((++count_assignments)>=5)
        return true;
    }
    else if(i_it->is_decl())
      return true;
  }

  return false;
}


existing_goals_filtert::existing_goals_filtert(
  message_handlert &message_handler,
  const std::string &filename,
  const irep_idt &mode):
  goal_filter_baset(message_handler)
{
  status() << "Load existing coverage goals\n";

  // check coverage file
  jsont json;
  if(parse_json(filename, message_handler, json))
  {
    throw filename+" file is not a valid json file";
  }

  // make sure that we have an array of elements
  if(!json.is_array())
  {
    std::stringstream s;
    s << "expecting an array in file " << filename
      << ", but got " << json;
    throw s.str();
  }

  // traverse the given JSON file
  for(const auto &each_goal : json.array)
  {
    source_locationt source_location;

    // check whether bytecodeIndex is provided for Java programs
    if(mode==ID_java)
    {
      if(each_goal["sourceLocation"]["bytecodeIndex"].is_null())
      {
        std::stringstream s;
        s << filename << " does not contain bytecodeIndex for" << each_goal;
        throw s.str();
      }

      // get and set the bytecodeIndex
      irep_idt bytecode_index=
        each_goal["sourceLocation"]["bytecodeIndex"].value;
      source_location.set_java_bytecode_index(bytecode_index);
    }
    else
    {
      if(each_goal["sourceLocation"]["file"].is_null())
      {
        std::stringstream s;
        s << filename << " does not contain file for" << each_goal;
        throw s.str();
      }

      // get and set the file
      irep_idt file=each_goal["sourceLocation"]["file"].value;
      source_location.set_file(file);

      if(each_goal["sourceLocation"]["function"].is_null())
      {
        std::stringstream s;
        s << filename << " does not contain function for" << each_goal;
        throw s.str();
      }

      // get and set the function
      irep_idt function=each_goal["sourceLocation"]["function"].value;
      source_location.set_function(function);

      if(each_goal["sourceLocation"]["line"].is_null())
      {
        std::stringstream s;
        s << filename << " does not contain line for" << each_goal;
        throw s.str();
      }

      // get and set the line
      irep_idt line=each_goal["sourceLocation"]["line"].value;
      source_location.set_line(line);
    }

    // store the existing goal
    goals[source_location]=false;
    status() << "  " << source_location << "\n";
  }
  status() << messaget::eom;
}

/// check whether we have an existing goal that does not match
/// an instrumented goal
void existing_goals_filtert::report_anomalies() const
{
  for(const auto &existing_loc : goals)
  {
    if(!existing_loc.second)
    {
      warning()
        << "Warning: unmatched existing goal "
        << existing_loc.first << messaget::eom;
    }
  }
}

/// compare the value of the current goal to the existing ones
/// and mark the matched existing goal
/// \param source_loc: source location of the current goal
/// \return true : if the given goal is non-existing, false : otherwise
bool existing_goals_filtert::operator()(
  const source_locationt &source_loc) const
{
  for(const auto &existing_loc : goals)
  {
    if((source_loc.get_file()==existing_loc.first.get_file()) &&
       (source_loc.get_function()==existing_loc.first.get_function()) &&
       (source_loc.get_line()==existing_loc.first.get_line()) &&
       (source_loc.get_java_bytecode_index().empty() ||
         (source_loc.get_java_bytecode_index()==
           existing_loc.first.get_java_bytecode_index())))
    {
      goals[existing_loc.first]=true;
      return false;
    }
  }
  return true;
}

/// Filter goals at source locations considered internal
/// \param source_location: source location of the current goal
/// \return true : if the given source location is considered internal
bool internal_goals_filtert::operator()(
  const source_locationt &source_location) const
{
  if(source_location.get_file().empty())
    return false;

  if(source_location.is_built_in())
    return false;

  return true;
}
