/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking

#include "bmc_checker.h"

#include "bmc_util.h"
#include "counterexample_beautification.h"

bmc_checkert::bmc_checkert(
  const optionst &options,
  ui_message_handlert &ui_message_handler,
  abstract_goto_modelt &goto_model)
  : multi_path_symex_checkert(options, ui_message_handler, goto_model),
    symex_run(false)
{
  solver_factoryt solvers(
    options,
    goto_model.get_symbol_table(),
    ui_message_handler,
    ui_message_handler.get_ui() == ui_message_handlert::uit::XML_UI);
  solver = solvers.get_solver();
}

goto_checkert::statust bmc_checkert::operator()(propertiest &properties)
{
  if(!symex_run)
  {
    perform_symex();
  }

  prop_convt &prop_conv = solver->prop_conv();
  log.status() << "Passing problem to "
           << prop_conv.decision_procedure_text() << messaget::eom;

  auto solver_start = std::chrono::steady_clock::now();

  if(!symex_run)
  {
    convert_symex_target_equation(equation, prop_conv, ui_message_handler);
    update_properties_from_symex_target_equation(properties);
    convert_goals();
    freeze_goal_variables();
    symex_run = true;
  }

  add_constraint_from_goals(properties);

  log.status() << "Running " << prop_conv.decision_procedure_text() << messaget::eom;

  decision_proceduret::resultt dec_result = prop_conv.dec_solve();

  update_properties_results_from_goals(properties, dec_result);

  auto solver_stop = std::chrono::steady_clock::now();
  log.status() << "Runtime decision procedure: "
           << std::chrono::duration<double>(
             solver_stop - solver_start).count()
           << "s" << messaget::eom;

  return dec_result == decision_proceduret::resultt::D_SATISFIABLE ?
         statust::HAVE_MORE : statust::DONE;
}

goto_tracet bmc_checkert::build_error_trace() const
{
  if(options.get_bool_option("beautify"))
  {
    counterexample_beautificationt()(
      dynamic_cast<boolbvt &>(solver->prop_conv()), equation);
  }
  namespacet ns(goto_model.get_symbol_table());
  goto_tracet error_trace;
  ::build_error_trace(error_trace, ns, equation, solver->prop_conv(), ui_message_handler);
  return error_trace;
}

void bmc_checkert::output_proof()
{
  namespacet ns(goto_model.get_symbol_table());
  output_graphml(equation, ns, options);
}

void bmc_checkert::output_error_witness(const goto_tracet &error_trace)
{
  namespacet ns(goto_model.get_symbol_table());
  output_graphml(error_trace, ns, options);
}

exprt bmc_checkert::goalt::as_expr() const
{
  std::vector<exprt> tmp;
  tmp.reserve(instances.size());
  for(const auto &inst : instances)
    tmp.push_back(literal_exprt(inst->cond_literal));
  return conjunction(tmp);
}

void bmc_checkert::update_properties_from_symex_target_equation(propertiest &properties)
{
  // get the conditions for these goals from formula
  // collect all 'instances' of the properties
  for(symex_target_equationt::SSA_stepst::iterator
        it = equation.SSA_steps.begin();
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
        property_id = id2string(
          it->source.pc->source_location.get_function())+".unwind."+
                      std::to_string(it->source.pc->loop_number);
        property_infot &property_info = properties[property_id];
        property_info.description = it->comment;
        property_info.location = it->source.pc;
      }
      else
        continue;

      // consider goal instance if it is in the given properties
      if(properties.count(property_id) > 0)
        goal_map[property_id].instances.push_back(it);
    }
  }
}

void bmc_checkert::convert_goals()
{
  for(auto &goal_pair : goal_map)
  {
    // Our goal is to falsify a property, i.e., we will
    // add the negation of the property as goal.
    goal_pair.second.condition = !solver->prop_conv().convert(goal_pair.second.as_expr());
  }
}

void bmc_checkert::freeze_goal_variables()
{
  for(const auto &goal_pair : goal_map)
  {
    if(!goal_pair.second.condition.is_constant())
      solver->prop_conv().set_frozen(goal_pair.second.condition);
  }
}

void bmc_checkert::add_constraint_from_goals(const propertiest &properties)
{
  exprt::operandst disjuncts;

  // cover at least one unknown goal

  for(const auto &goal_pair : goal_map)
  {
    const auto &result = properties.at(goal_pair.first).result;
    if((result == property_resultt::NOT_REACHED ||
        result == property_resultt::UNKNOWN) &&
       !goal_pair.second.condition.is_false())
      disjuncts.push_back(literal_exprt(goal_pair.second.condition));
  }

  // this is 'false' if there are no disjuncts
  solver->prop_conv().set_to_true(disjunction(disjuncts));
}

void bmc_checkert::update_properties_results_from_goals(
  propertiest &properties, decision_proceduret::resultt dec_result)
{
  switch(dec_result)
  {
    case decision_proceduret::resultt::D_SATISFIABLE:
      for(auto &goal_pair : goal_map)
      {
        if(solver->prop_conv().l_get(goal_pair.second.condition).is_true())
          properties[goal_pair.first].result |= property_resultt::FAIL;
      }
      break;
    case decision_proceduret::resultt::D_UNSATISFIABLE:
      for(auto &property_pair : properties)
      {
        if(property_pair.second.result == property_resultt::UNKNOWN)
          property_pair.second.result |= property_resultt::PASS;
      }
      break;
    case decision_proceduret::resultt::D_ERROR:
      for(auto &property_pair : properties)
      {
        if(property_pair.second.result == property_resultt::UNKNOWN)
          property_pair.second.result |= property_resultt::ERROR;
      }
      break;
  }
}
