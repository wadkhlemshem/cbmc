/*******************************************************************\

Module: Goto Verifier for Coverage Goals

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Goto Verifier for Coverage Goals

#ifndef CPROVER_GOTO_CHECKER_COVER_GOALS_VERIFIER_H
#define CPROVER_GOTO_CHECKER_COVER_GOALS_VERIFIER_H

#include "goto_verifier.h"

#include "goto_checker.h"
#include "properties.h"

template<class goto_checkerT, class test_case_generatorT>
class cover_goals_verifiert : public goto_verifiert
{
public:
  cover_goals_verifiert(
    const optionst &options,
    ui_message_handlert &ui_message_handler,
    abstract_goto_modelt &goto_model)
  : goto_verifiert(options, ui_message_handler),
    goto_model(goto_model),
    goto_checker(options, ui_message_handler, goto_model)
  {
    properties = std::move(initialize_properties(goto_model));
  }

  resultt operator()() override
  {
    // have we got anything to check? otherwise we return PASS
    if(!has_properties_to_check(properties))
      return resultt::PASS;

    test_case_generatorT test_case_generator(options, goto_model,
                                             ui_message_handler);
    while(goto_checker(properties) != goto_checkert::statust::DONE)
    {
      namespacet ns(goto_model.get_symbol_table());
      const goto_tracet &goto_trace = goto_checker.build_error_trace();
      result()
        << test_case_generator(goto_trace)->to_json(ns, goto_trace, true);
    }
    return determine_result(properties);
  }

protected:
  abstract_goto_modelt &goto_model;
  goto_checkerT goto_checker;
};

#endif // CPROVER_GOTO_CHECKER_COVER_GOALS_VERIFIER_H
