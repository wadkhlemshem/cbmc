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


void existing_goalst::load(
  const std::string &filename,
  message_handlert &message_handler,
  existing_goalst &existing_goals,
  const irep_idt &mode)
{
  messaget message(message_handler);

  message.status() << "Load existing coverage goals\n";

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
    existing_goals.goals[source_location]=false;
    message.status() << "  " << source_location << "\n";
  }
  message.status() << messaget::eom;
}

/// check whether we have an existing goal that does not match
/// an instrumented goal
/// \param msg: Message stream
void existing_goalst::report_anomalies(message_handlert &message_handler)
{
  messaget msg(message_handler);

  for(const auto &existing_loc : goals)
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
/// and mark the matched existing goal
/// \param source_loc: source location of the current goal
/// \return true : if the current goal exists false : otherwise
bool existing_goalst::contains(const source_locationt &source_loc)
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
      return true;
    }
  }
  return false;
}
