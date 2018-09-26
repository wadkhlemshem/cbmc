/*******************************************************************\

Module: Goto Checker using Bounded Model Checking

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Bounded Model Checking

#ifndef CPROVER_GOTO_CHECKER_BMC_CHECKER_H
#define CPROVER_GOTO_CHECKER_BMC_CHECKER_H

#include "multi_path_symex_checker.h"

#include "solver_factory.h"

class bmc_checkert : public multi_path_symex_checkert
{
public:
  bmc_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  statust operator()(propertiest &) override;

  goto_tracet build_error_trace() const override;

  void output_error_witness(const goto_tracet &) override;

  void output_proof() override;

protected:
  std::unique_ptr<solver_factoryt::solvert> solver;

  struct goalt
  {
    // a property holds if all instances of it are true
    typedef std::vector<symex_target_equationt::SSA_stepst::iterator>
      instancest;
    instancest instances;
    literalt condition;

    exprt as_expr() const;
  };

  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;

  bool symex_run;

  void update_properties_from_symex_target_equation(propertiest &properties);
  void convert_goals();
  void freeze_goal_variables();
  void add_constraint_from_goals(const propertiest &properties);
  void update_properties_results_from_goals(
    propertiest &properties, decision_proceduret::resultt dec_result);
};

#endif // CPROVER_GOTO_CHECKER_BMC_CHECKER_H
