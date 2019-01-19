/*******************************************************************\

Module: Goto Checker using Multi-Path Symbolic Execution

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Checker using Multi-Path Symbolic Execution

#ifndef CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H
#define CPROVER_GOTO_CHECKER_MULTI_PATH_SYMEX_CHECKER_H

#include "goto_trace_provider.h"
#include "multi_path_symex_only_checker.h"
#include "witness_provider.h"
#include "solver_factory.h"

class multi_path_symex_checkert
  : public multi_path_symex_only_checkert,
    public goto_trace_providert,
    public witness_providert
{
public:
  multi_path_symex_checkert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model);

  incremental_goto_checker_resultt operator()(propertiest &) override;

  goto_tracet build_trace() const override;
  const namespacet &get_namespace() const override;

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
  std::vector<irep_idt> update_properties_status_from_goals(
    propertiest &properties,
    decision_proceduret::resultt dec_result);
};

#endif // CPROVER_GOTO_CHECKER_BMC_CHECKER_H
