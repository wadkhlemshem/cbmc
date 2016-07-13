#include <iostream>
#include <functional>

#include <util/message.h>
#include <cbmc/bmc.h>

#include <java_bytecode/java_entry_point.h>
#include <test_gen/java_test_source_factory.h>
#include <test_gen/java_test_case_generator.h>

namespace
{
bool contains(const std::string &id, const char * const needle)
{
  return std::string::npos != id.find(needle);
}

bool is_meta(const irep_idt &id)
{
  const std::string &str=id2string(id);
  return contains(str, "$assertionsDisabled")
      || contains(str, "symex_dynamic::");
}

inputst generate_inputs(const symbol_tablet &st, const goto_functionst &gf,
    const goto_tracet &trace, interpretert::list_input_varst& opaque_function_returns)
{
  interpretert interpreter(st, gf);
  inputst res(interpreter.load_counter_example_inputs(trace, opaque_function_returns));
  for (inputst::const_iterator it(res.begin()); it != res.end();)
    if (is_meta(it->first)) it=res.erase(it);
    else ++it;
  return res;
}

const irep_idt &get_entry_function_id(const goto_functionst &gf)
{
  typedef goto_functionst::function_mapt function_mapt;
  const function_mapt &fm=gf.function_map;
  const irep_idt start(goto_functionst::entry_point());
  const function_mapt::const_iterator entry_func=fm.find(start);
  assert(fm.end() != entry_func);
  const goto_programt::instructionst &in=entry_func->second.body.instructions;
  typedef goto_programt::instructionst::const_reverse_iterator reverse_target;
  const reverse_target last=in.rbegin();
  const reverse_target end=in.rend();
  assert(end != last);
  const reverse_target call=std::next(last);
  assert(end != call);
  const code_function_callt &func_call=to_code_function_call(call->code);
  const exprt &func_expr=func_call.function();
  return to_symbol_expr(func_expr).get_identifier();
}

typedef std::function<
  std::string(const symbol_tablet &, const irep_idt &, const inputst &, const interpretert::list_input_varst&)> test_case_generatort;

void generate_test_case(const optionst &options, const symbol_tablet &st,
    const goto_functionst &gf, const goto_tracet &trace,
    const test_case_generatort generate, std::string test_case_name="")
{

  interpretert::list_input_varst opaque_function_returns;
  
  const inputst inputs(generate_inputs(st, gf, trace, opaque_function_returns));
  const irep_idt &entry_func_id=get_entry_function_id(gf);
  const std::string source(generate(st, entry_func_id, inputs, opaque_function_returns));
  std::string out_file_name=options.get_option("outfile");
  if(out_file_name.empty())
  {
    if(!test_case_name.empty())
      std::cout << "Test case: " << test_case_name << std::endl;
    std::cout << source;
  }
  else
  {
    assert(!test_case_name.empty());
    out_file_name+='_';
    out_file_name+=test_case_name;
    std::ofstream(out_file_name.c_str()) << source;
  }
}

int generate_test_case(optionst &options, const symbol_tablet &st,
    const goto_functionst &gf, bmct &bmc, const test_case_generatort generate)
{
  options.set_option("stop-on-fail", true);
  switch (bmc(gf))
  {
  case safety_checkert::SAFE:
    return TEST_CASE_FAIL;
  case safety_checkert::ERROR:
    return TEST_CASE_ERROR;
  case safety_checkert::UNSAFE:
  default:
  {
    const goto_tracet &trace=bmc.safety_checkert::error_trace;
    generate_test_case(options, st, gf, trace, generate);
    return TEST_CASE_SUCCESS;
  }
  }
}
}

void generate_java_test_case(const optionst &options, const symbol_tablet &st,
    const goto_functionst &gf, const goto_tracet &trace,
    const std::string &name)
{
  const test_case_generatort source_gen=generate_java_test_case_from_inputs;
  generate_test_case(options, st, gf, trace, source_gen, name);
}

int generate_java_test_case(optionst &o, const symbol_tablet &st,
    const goto_functionst &gf, bmct &bmc)
{
  const test_case_generatort source_gen=generate_java_test_case_from_inputs;
  return generate_test_case(o, st, gf, bmc, source_gen);
}
