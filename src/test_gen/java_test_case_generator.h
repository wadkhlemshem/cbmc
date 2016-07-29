/*******************************************************************

 Module: Counterexample-Guided Inductive Synthesis

 Author: Daniel Kroening, kroening@kroening.com
         Pascal Kesseli, pascal.kesseil@cs.ox.ac.uk

\*******************************************************************/

#ifndef JAVA_TEST_CASE_GENERATOR_H_
#define JAVA_TEST_CASE_GENERATOR_H_

#include <string>

#define TEST_CASE_SUCCESS 0
#define TEST_CASE_FAIL 1
#define TEST_CASE_ERROR 10

//static int out_file_no = 0;

#include <util/options.h>

/**
 * @brief
 *
 * @details
 *
 * @param options
 * @param st
 * @param gf
 * @param bmc
 *
 * @return
 */
int generate_java_test_case(
    class optionst &options,
    const class symbol_tablet &st,
    const class goto_functionst &gf,
    class bmct &bmc);

/**
 * @brief
 *
 * @details
 *
 * @param options
 * @param st
 * @param gf
 * @param trace
 * @param name
 */
const std::string generate_java_test_case(
    const optionst &options,
    const symbol_tablet &st,
    const goto_functionst &gf,
    const class goto_tracet &trace,
    const std::string &property);
#endif /* JAVA_TEST_CASE_GENERATOR_H_ */
