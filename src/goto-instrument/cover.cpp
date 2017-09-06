/*******************************************************************\

Module: Coverage Instrumentation

Author: Daniel Kroening

Date: May 2016

\*******************************************************************/

/// \file
/// Coverage Instrumentation


#include "cover.h"

#include <iterator>
#include <unordered_set>
#include <regex>

#include <util/config.h>
#include <util/cprover_prefix.h>
#include <util/format_number_range.h>
#include <util/message.h>
#include <util/prefix.h>

#include "cover_basic_blocks.h"
#include "cover_filter.h"
#include "cover_instrument_location.h"
#include "cover_instrument_branch.h"
#include "cover_instrument_condition.h"
#include "cover_instrument_decision.h"
#include "cover_instrument_mcdc.h"
#include "cover_instrument_other.h"

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program,
  coverage_criteriont criterion,
  message_handlert &message_handler,
  coverage_goalst &goals)
{
  // ignore if built-in library
  if(!goto_program.instructions.empty() &&
     goto_program.instructions.front().source_location.is_built_in())
    return;

  const namespacet ns(symbol_table);
  cover_basic_blockst basic_blocks(goto_program);
  basic_blocks.select_unique_java_bytecode_indices(
    goto_program, message_handler);
  basic_blocks.report_block_anomalies(goto_program, message_handler);

  Forall_goto_program_instructions(i_it, goto_program)
  {
    switch(criterion)
    {
    case coverage_criteriont::ASSERTION:
      cover_instrument_assertion(i_it);
      break;

    case coverage_criteriont::COVER:
      cover_instrument_cover(ns, i_it);
      break;

    case coverage_criteriont::LOCATION:
      cover_instrument_location(goto_program, i_it, basic_blocks, goals);
      break;

    case coverage_criteriont::BRANCH:
      cover_instrument_branch(goto_program, i_it, basic_blocks);
      break;

    case coverage_criteriont::CONDITION:
      cover_instrument_condition(ns, goto_program, i_it);
      break;

    case coverage_criteriont::DECISION:
      cover_instrument_decision(ns, goto_program, i_it);
      break;

    case coverage_criteriont::MCDC:
      cover_instrument_mcdc(ns, goto_program, i_it);
      break;

    case coverage_criteriont::PATH:
      cover_instrument_path(i_it);
      break;
    }
  }
}

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_programt &goto_program,
  coverage_criteriont criterion,
  message_handlert &message_handler)
{
  coverage_goalst goals; // empty already covered goals
  instrument_cover_goals(
    symbol_table,
    goto_program,
    criterion,
    message_handler,
    goals);
}

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  coverage_criteriont criterion,
  message_handlert &message_handler,
  coverage_goalst &goals,
  bool ignore_trivial,
  const std::string &cover_include_pattern)
{
  std::smatch string_matcher;
  std::regex regex_matcher(cover_include_pattern);
  bool do_include_pattern_match=!cover_include_pattern.empty();

  Forall_goto_functions(f_it, goto_functions)
  {
    // exclude trivial coverage goals of a goto program
    if(ignore_trivial && program_is_trivial(f_it->second.body))
      continue;

    if(f_it->first==goto_functions.entry_point() ||
       f_it->first==(CPROVER_PREFIX "initialize") ||
       f_it->second.is_hidden() ||
       (do_include_pattern_match &&
        !std::regex_match(
          id2string(f_it->first), string_matcher, regex_matcher)) ||
       // ignore Java array built-ins
       has_prefix(id2string(f_it->first), "java::array"))
      continue;

    instrument_cover_goals(
      symbol_table,
      f_it->second.body,
      criterion,
      message_handler,
      goals);
  }
}

void instrument_cover_goals(
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  coverage_criteriont criterion,
  message_handlert &message_handler)
{
  // empty set of existing goals
  coverage_goalst goals;
  instrument_cover_goals(
    symbol_table,
    goto_functions,
    criterion,
    message_handler,
    goals,
    false,
    "");
}

bool instrument_cover_goals(
  const cmdlinet &cmdline,
  const symbol_tablet &symbol_table,
  goto_functionst &goto_functions,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  std::list<std::string> criteria_strings=cmdline.get_values("cover");
  std::set<coverage_criteriont> criteria;
  bool keep_assertions=false;

  for(const auto &criterion_string : criteria_strings)
  {
    coverage_criteriont c;

    if(criterion_string=="assertion" || criterion_string=="assertions")
    {
      keep_assertions=true;
      c=coverage_criteriont::ASSERTION;
    }
    else if(criterion_string=="path" || criterion_string=="paths")
      c=coverage_criteriont::PATH;
    else if(criterion_string=="branch" || criterion_string=="branches")
      c=coverage_criteriont::BRANCH;
    else if(criterion_string=="location" || criterion_string=="locations")
      c=coverage_criteriont::LOCATION;
    else if(criterion_string=="decision" || criterion_string=="decisions")
      c=coverage_criteriont::DECISION;
    else if(criterion_string=="condition" || criterion_string=="conditions")
      c=coverage_criteriont::CONDITION;
    else if(criterion_string=="mcdc")
      c=coverage_criteriont::MCDC;
    else if(criterion_string=="cover")
      c=coverage_criteriont::COVER;
    else
    {
      msg.error() << "unknown coverage criterion "
                  << '\'' << criterion_string << '\''
                  << messaget::eom;
      return true;
    }

    criteria.insert(c);
  }

  if(keep_assertions && criteria_strings.size()>1)
  {
    msg.error() << "assertion coverage cannot currently be used together with "
                << "other coverage criteria" << messaget::eom;
    return true;
  }

  msg.status() << "Rewriting existing assertions as assumptions"
               << messaget::eom;

  if(!keep_assertions)
  {
    // turn assertions (from generic checks) into assumptions
    Forall_goto_functions(f_it, goto_functions)
    {
      goto_programt &body=f_it->second.body;
      Forall_goto_program_instructions(i_it, body)
      {
        if(i_it->is_assert())
          i_it->type=goto_program_instruction_typet::ASSUME;
      }
    }
  }

  // cover entry point function only
  std::string cover_include_pattern=cmdline.get_value("cover-include-pattern");
  if(cmdline.isset("cover-function-only"))
  {
    std::regex special_characters(
      "\\.|\\\\|\\*|\\+|\\?|\\{|\\}|\\[|\\]|\\(|\\)|\\^|\\$|\\|");
    cover_include_pattern=
      ".*"+std::regex_replace(config.main, special_characters, "\\$&")+".*";
  }

  // check existing test goals
  coverage_goalst existing_goals;
  if(cmdline.isset("existing-coverage"))
  {
    // get the mode to ensure invariants
    // (e.g., bytecodeIndex for Java programs)
    namespacet ns(symbol_table);
    const irep_idt &mode=ns.lookup(goto_functions.entry_point()).mode;

    // get file with covered test goals
    const std::string coverage=cmdline.get_value("existing-coverage");
    // get a coverage_goalst object
    if(coverage_goalst::get_coverage_goals(
       coverage, message_handler, existing_goals, mode))
    {
      msg.error() << "Loading existing coverage goals failed" << messaget::eom;
      return true;
    }
  }

  msg.status() << "Instrumenting coverage goals" << messaget::eom;

  for(const auto &criterion : criteria)
  {
    instrument_cover_goals(
      symbol_table,
      goto_functions,
      criterion,
      message_handler,
      existing_goals,
      cmdline.isset("no-trivial-tests"),
      cover_include_pattern);
  }

  // check whether all existing goals match with instrumented goals
  existing_goals.check_existing_goals(message_handler);

  if(cmdline.isset("cover-traces-must-terminate"))
  {
    // instrument an additional goal in CPROVER_START. This will rephrase
    // the reachability problem  by asking BMC to provide a solution that
    // satisfies a goal while getting to the end of the program-under-test.
    const auto sf_it=
      goto_functions.function_map.find(goto_functions.entry_point());
    if(sf_it==goto_functions.function_map.end())
    {
      msg.error() << "cover-traces-must-terminate: invalid entry point ["
                  << goto_functions.entry_point() << "]"
                  << messaget::eom;
      return true;
    }

    cover_instrument_end_of_function(sf_it->first, sf_it->second.body);
  }

  goto_functions.update();
  return false;
}

bool instrument_cover_goals(
  const cmdlinet &cmdline,
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  return instrument_cover_goals(
    cmdline,
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler);
}
