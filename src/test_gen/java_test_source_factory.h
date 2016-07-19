/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef JAVA_TEST_SOURCE_FACTORY_H_
#define JAVA_TEST_SOURCE_FACTORY_H_

#include <util/expr.h>
#include <goto-programs/interpreter_class.h>

/**
 * @brief
 *
 * @details
 */
typedef std::map<const irep_idt, exprt> inputst;

/**
 * @brief
 *
 * @details
 *
 * @param st
 * @param func_id
 * @param inputs
 *
 * @return
 */
std::string generate_java_test_case_from_inputs(
    const class symbol_tablet &st,
    const irep_idt &func_id,
    inputst inputs,
    const interpretert::list_input_varst& opaque_function_returns,
    bool disable_mocks);

std::string func_name(const symbolt &symbol);

#endif /* JAVA_TEST_SOURCE_FACTORY_H_ */
