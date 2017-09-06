/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

\*******************************************************************/

/// \file
/// Filters for the Coverage Instrumentation

#include "cover_filter.h"

#include <json/json_parser.h>

#include <util/message.h>


/// Call a goto_program trivial unless it has: * Any declarations * At least 2
/// branches * At least 5 assignments
/// \par parameters: Program `goto_program`
/// \return Returns true if trivial
bool program_is_trivial(const goto_programt &goto_program)
{
  unsigned long count_assignments=0, count_goto=0;
  forall_goto_program_instructions(i_it, goto_program)
  {
    if(i_it->is_goto())
    {
      if((++count_goto)>=2)
        return false;
    }
    else if(i_it->is_assign())
    {
      if((++count_assignments)>=5)
        return false;
    }
    else if(i_it->is_decl())
      return false;
  }

  return true;
}


bool coverage_goalst::get_coverage_goals(
  const std::string &coverage_file,
  message_handlert &message_handler,
  coverage_goalst &goals,
  const irep_idt &mode)
{
  messaget message(message_handler);
  jsont json;
  source_locationt source_location;

  message.status() << "Load existing coverage goals\n";

  // check coverage file
  if(parse_json(coverage_file, message_handler, json))
  {
    message.error() << coverage_file << " file is not a valid json file"
                    << messaget::eom;
    return true;
  }

  // make sure that we have an array of elements
  if(!json.is_array())
  {
    message.error() << "expecting an array in the " <<  coverage_file
                    << " file, but got "
                    << json << messaget::eom;
    return true;
  }

  // traverse the given JSON file
  for(const auto &each_goal : json.array)
  {
    // ensure minimal requirements for a goal entry
    PRECONDITION(
      (!each_goal["goal"].is_null()) ||
      (!each_goal["sourceLocation"]["bytecodeIndex"].is_null()) ||
      (!each_goal["sourceLocation"]["file"].is_null() &&
       !each_goal["sourceLocation"]["function"].is_null() &&
       !each_goal["sourceLocation"]["line"].is_null()));

    // check whether bytecodeIndex is provided for Java programs
    if(mode==ID_java &&
       each_goal["sourceLocation"]["bytecodeIndex"].is_null())
    {
      messaget message(message_handler);
      message.error() << coverage_file
                      << " file does not contain bytecodeIndex"
                      << messaget::eom;
      return true;
    }

    if(!each_goal["sourceLocation"]["bytecodeIndex"].is_null())
    {
      // get and set the bytecodeIndex
      irep_idt bytecode_index=
        each_goal["sourceLocation"]["bytecodeIndex"].value;
      source_location.set_java_bytecode_index(bytecode_index);
    }

    if(!each_goal["sourceLocation"]["file"].is_null())
    {
      // get and set the file
      irep_idt file=each_goal["sourceLocation"]["file"].value;
      source_location.set_file(file);
    }

    if(!each_goal["sourceLocation"]["function"].is_null())
    {
      // get and set the function
      irep_idt function=each_goal["sourceLocation"]["function"].value;
      source_location.set_function(function);
    }

    if(!each_goal["sourceLocation"]["line"].is_null())
    {
      // get and set the line
      irep_idt line=each_goal["sourceLocation"]["line"].value;
      source_location.set_line(line);
    }

    // store the existing goal
    goals.add_goal(source_location);
    message.status() << "  " << source_location << "\n";
  }
  message.status() << messaget::eom;

  return false;
}

/// store existing goal
/// \param goal: source location of the existing goal
void coverage_goalst::add_goal(source_locationt goal)
{
  existing_goals[goal]=false;
}

/// check whether we have an existing goal that does not match
/// an instrumented goal
/// \param msg: Message stream
void coverage_goalst::check_existing_goals(message_handlert &message_handler)
{
  messaget msg(message_handler);

  for(const auto &existing_loc : existing_goals)
  {
    if(!existing_loc.second)
    {
      msg.warning()
        << "Warning: unmatched existing goal "
        << existing_loc.first << messaget::eom;
    }
  }
}

/// compare the value of the current goal to the existing ones
/// \param source_loc: source location of the current goal
/// \return true : if the current goal exists false : otherwise
bool coverage_goalst::is_existing_goal(source_locationt source_loc)
{
  for(const auto &existing_loc : existing_goals)
  {
    if((source_loc.get_file()==existing_loc.first.get_file()) &&
       (source_loc.get_function()==existing_loc.first.get_function()) &&
       (source_loc.get_line()==existing_loc.first.get_line()) &&
       (source_loc.get_java_bytecode_index().empty() ||
         (source_loc.get_java_bytecode_index()==
           existing_loc.first.get_java_bytecode_index())))
    {
      existing_goals[existing_loc.first]=true;
      return true;
    }
  }
  return false;
}

