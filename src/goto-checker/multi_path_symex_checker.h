/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H

#include "multi_path_symex_only_checker.h"

#include "solver_factory.h"

class multi_path_symex_checkert : public multi_path_symex_only_checkert
{
public:
  multi_path_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  resultt operator()(propertiest &) override;

  goto_tracet build_error_trace() const override;

  void output_error_witness(const goto_tracet &) override;

  void output_proof() override;

protected:
  std::unique_ptr<solver_factoryt::solvert> solver;

  struct goalt
  {
    // a property holds if all instances of it are true
    std::vector<symex_target_equationt::SSA_stepst::iterator> instances;
    literalt condition;

    exprt as_expr() const;
  };

  typedef std::map<irep_idt, goalt> goal_mapt;
  goal_mapt goal_map;

  bool symex_has_run;

  void update_properties_goals_from_symex_target_equation(propertiest &properties);
  void convert_goals();
  void freeze_goal_variables();
  void add_constraint_from_goals(const propertiest &properties);
  void update_properties_status_from_goals(
    propertiest &properties,
    decision_proceduret::resultt dec_result);
};

#endif // CPROVER_GOTO_CHECKER_BMC_CHECKER_H
