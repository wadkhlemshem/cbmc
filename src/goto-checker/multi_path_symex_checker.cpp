/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking

#include "multi_path_symex_checker.h"

#include <chrono>

#include "bmc_util.h"
#include "counterexample_beautification.h"

multi_path_symex_checkert::multi_path_symex_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : multi_path_symex_only_checkert(options, ui_message_handler, goto_model),
    symex_has_run(false)
{
  solver_factoryt solvers(
    options,
    ns,
    ui_message_handler,
    ui_message_handler.get_ui() == ui_message_handlert::uit::XML_UI);
  solver = solvers.get_solver();
}

incremental_goto_checkert::resultt multi_path_symex_checkert::
operator()(propertiest &properties)
{
  if(!symex_has_run)
  {
    perform_symex();
  }

  prop_convt &prop_conv = solver->prop_conv();
  log.status() << "Passing problem to " << prop_conv.decision_procedure_text()
               << messaget::eom;

  auto solver_start = std::chrono::steady_clock::now();

  if(!symex_has_run)
  {
    convert_symex_target_equation(equation, prop_conv, ui_message_handler);
    update_properties_status_from_symex_target_equation(properties, equation);
    update_properties_goals_from_symex_target_equation(properties);
    convert_goals();
    freeze_goal_variables();
    symex_has_run = true;
  }

  add_constraint_from_goals(properties);

  log.status() << "Running " << prop_conv.decision_procedure_text()
               << messaget::eom;

  decision_proceduret::resultt dec_result = prop_conv.dec_solve();

  update_properties_status_from_goals(properties, dec_result);

  auto solver_stop = std::chrono::steady_clock::now();
  log.status()
    << "Runtime decision procedure: "
    << std::chrono::duration<double>(solver_stop - solver_start).count() << "s"
    << messaget::eom;

  return dec_result == decision_proceduret::resultt::D_SATISFIABLE
           ? resultt::FOUND_FAIL
           : resultt::DONE;
}

goto_tracet multi_path_symex_checkert::build_error_trace() const
{
  if(options.get_bool_option("beautify"))
  {
    counterexample_beautificationt()(
      dynamic_cast<boolbvt &>(solver->prop_conv()), equation);
  }
  goto_tracet error_trace;
  ::build_error_trace(
    error_trace, ns, equation, solver->prop_conv(), ui_message_handler);
  return error_trace;
}

void multi_path_symex_checkert::output_proof()
{
  output_graphml(equation, ns, options);
}

void multi_path_symex_checkert::output_error_witness(
  const goto_tracet &error_trace)
{
  output_graphml(error_trace, ns, options);
}

exprt multi_path_symex_checkert::goalt::as_expr() const
{
  std::vector<exprt> tmp;
  tmp.reserve(instances.size());
  for(const auto &inst : instances)
    tmp.push_back(literal_exprt(inst->cond_literal));
  return conjunction(tmp);
}

void multi_path_symex_checkert::update_properties_goals_from_symex_target_equation(
  propertiest &properties)
{
  // get the conditions for these goals from formula
  // collect all 'instances' of the properties
  for(symex_target_equationt::SSA_stepst::iterator it =
        equation.SSA_steps.begin();
      it != equation.SSA_steps.end();
      ++it)
  {
    if(it->is_assert())
    {
      irep_idt property_id;

      if(it->source.pc->is_assert())
        property_id = it->source.pc->source_location.get_property_id();
      else if(it->source.pc->is_goto())
      {
        // this is likely an unwinding assertion
        property_id = id2string(it->source.pc->source_location.get_function()) +
                      ".unwind." + std::to_string(it->source.pc->loop_number);
        properties.emplace(
          property_id,
          property_infot{
            it->source.pc, it->comment, property_statust::NOT_CHECKED});
      }
      else
        continue;

      // consider goal instance if it is in the given properties
      auto property_pair_it = properties.find(property_id);
      if(
        property_pair_it != properties.end() &&
        is_property_to_check(property_pair_it->second.status))
      {
        // it's going to be checked, but we don't know the status yet
        property_pair_it->second.status |= property_statust::UNKNOWN;
        goal_map[property_id].instances.push_back(it);
      }
    }
  }
}

void multi_path_symex_checkert::convert_goals()
{
  for(auto &goal_pair : goal_map)
  {
    // Our goal is to falsify a property, i.e., we will
    // add the negation of the property as goal.
    goal_pair.second.condition =
      !solver->prop_conv().convert(goal_pair.second.as_expr());
  }
}

void multi_path_symex_checkert::freeze_goal_variables()
{
  for(const auto &goal_pair : goal_map)
  {
    if(!goal_pair.second.condition.is_constant())
      solver->prop_conv().set_frozen(goal_pair.second.condition);
  }
}

void multi_path_symex_checkert::add_constraint_from_goals(
  const propertiest &properties)
{
  exprt::operandst disjuncts;

  // cover at least one unknown goal

  for(const auto &goal_pair : goal_map)
  {
    if(
      is_property_to_check(properties.at(goal_pair.first).status) &&
      !goal_pair.second.condition.is_false())
    {
      disjuncts.push_back(literal_exprt(goal_pair.second.condition));
    }
  }

  // this is 'false' if there are no disjuncts
  solver->prop_conv().set_to_true(disjunction(disjuncts));
}

void multi_path_symex_checkert::update_properties_status_from_goals(
  propertiest &properties,
  decision_proceduret::resultt dec_result)
{
  switch(dec_result)
  {
  case decision_proceduret::resultt::D_SATISFIABLE:
    for(auto &goal_pair : goal_map)
    {
      if(solver->prop_conv().l_get(goal_pair.second.condition).is_true())
        properties.at(goal_pair.first).status |= property_statust::FAIL;
    }
    break;
  case decision_proceduret::resultt::D_UNSATISFIABLE:
    for(auto &property_pair : properties)
    {
      if(property_pair.second.status == property_statust::UNKNOWN)
        property_pair.second.status |= property_statust::PASS;
    }
    break;
  case decision_proceduret::resultt::D_ERROR:
    for(auto &property_pair : properties)
    {
      if(property_pair.second.status == property_statust::UNKNOWN)
        property_pair.second.status |= property_statust::ERROR;
    }
    break;
  }
}
