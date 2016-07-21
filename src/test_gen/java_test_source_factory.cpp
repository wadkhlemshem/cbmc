
#include <ctype.h>

#include <algorithm>
#include <set>
#include <iostream>

#include <util/substitute.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/symbol_table.h>
#include <util/namespace.h>

#include <java_bytecode/expr2java.h>

#include <test_gen/java_test_source_factory.h>
#include <test_gen/mock_environment_builder.h>

#define INDENT_SPACES "  "
#define JAVA_NS_PREFIX_LEN 6u

namespace
{

  class java_call_descriptor;
  
// Class to carry mock_classes and the mock environment builder around so that any
// attempt to generate a new object can easily find out whether it needs a real
// object or a mock.
class reference_factoryt {

public:

  std::set<std::string> mock_classes;
  mock_environment_builder mockenv_builder;

  reference_factoryt(int indent) : mockenv_builder(indent) {}
  void add_value(std::string &result, const symbol_tablet &st,
		 const exprt &value, const std::string var_name="");
  void add_value(std::string &result, const symbol_tablet &st,
		 const struct_exprt &value, const std::string &this_name);
  void add_assign_value(std::string &result, const symbol_tablet &st,
			const symbolt &symbol, const exprt &value);
  void add_global_state_assignments(std::string &result, const symbol_tablet &st,
				    inputst &in);
  bool add_func_call_parameters(std::string &result, const symbol_tablet &st,
				const irep_idt &func_id, inputst &inputs);
  void add_mock_call(const interpretert::function_assignments_contextt,
		     const java_call_descriptor& desc, const symbol_tablet&);
  void add_mock_objects(const symbol_tablet &st,
			const interpretert::list_input_varst& opaque_function_returns);
  
};
  
std::string &indent(std::string &result, const size_t num_indent=1u)
{
  for (size_t i=0u; i < num_indent; ++i)
    result+=INDENT_SPACES;
  return result;
}

void add_test_class_name(std::string &result, const std::string &func_name)
{
  result+="public class ";
  result+=func_name;
  result+="Test {\n";
  indent(result)+="@org.junit.Test public void test";
  result+=func_name;
  result+="() throws Exception {\n";
}

void add_symbol(std::string &result, const symbolt &s)
{
  // XXX: Should be expr2java(...) once functional.
  const irep_idt &n=s.pretty_name.empty() ? s.base_name : s.pretty_name;
  result+=id2string(n);
}

void add_qualified_class_name(std::string &result, const namespacet &ns,
    const typet &type)
{
  if (ID_symbol == type.id())
  {
    const std::string &id=id2string(to_symbol_type(type).get_identifier());
    assert(id.size() >= JAVA_NS_PREFIX_LEN);
    result+=id.substr(JAVA_NS_PREFIX_LEN);
  } else result+=id2string(to_struct_type(type).get_tag());
}

void add_decl_from_type(std::string& result, const symbol_tablet &st, const typet &type, bool* out_is_primitive = 0)
{
  if(out_is_primitive)
    *out_is_primitive = false;
  
  const namespacet ns(st);
  const typet &subt=type.subtype();
  const irep_idt &type_id=type.id();
  if (ID_symbol == type_id || ID_struct == type_id) add_qualified_class_name(
      result, ns, type);
  else if (ID_pointer == type_id) add_qualified_class_name(result, ns, subt);
  else {
    if(out_is_primitive)
      *out_is_primitive = true;
    result+=type2java(type, ns);
  }
}

void add_decl_with_init_prefix(std::string &result, const symbol_tablet &st,
			       const symbolt &symbol)
{
  add_decl_from_type(result, st, symbol.type);
  result+=' ';
}

void expr2java(std::string &result, const exprt &value, const namespacet &ns)
{
  std::string item=expr2java(value, ns);
  result+=item.substr(0, item.find('!', 0));
}

void reference_factoryt::add_value(std::string &result, const symbol_tablet &st, const exprt &value,
    const std::string var_name)
{
  const namespacet ns(st);
  const irep_idt &id=value.id();
  if (ID_address_of == id) add_value(result, st,
      to_address_of_expr(value).object());
  else if (ID_struct == id) add_value(result, st, to_struct_expr(value),
      var_name);
  else if (ID_constant == id && !value.operands().empty()) add_value(result, st,
      value.op0(), var_name);
  else expr2java(result, value, ns);
}

bool is_class_name_comp(const struct_typet::componentt &comp,
    const size_t index)
{
  return ID_string == comp.type().id() && index == 0;
}

class member_factoryt
{
  std::string &result;
  const symbol_tablet &st;
  const std::string &this_name;
  const struct_typet::componentst &comps;
  size_t comp_index;
  bool line_terminated;
  reference_factoryt& ref_factory;

public:
  member_factoryt(std::string &result, const symbol_tablet &st,
      const std::string &this_name, const typet &type, reference_factoryt& _ref_factory) :
      result(result), st(st), this_name(this_name), comps(
          to_struct_type(type).components()), comp_index(0u), line_terminated(
          true), ref_factory(_ref_factory)
  {
  }

  bool is_line_terminated() const
  {
    return line_terminated;
  }

  void operator()(const exprt &value)
  {
    assert(comp_index < comps.size());
    if (ID_struct == value.id())
    {
      member_factoryt mem_fac(result, st, this_name, value.type(), ref_factory);
      const struct_exprt::operandst &ops=value.operands();
      std::for_each(ops.begin(), ops.end(), mem_fac);
      if (result.back() != '\n') result+=";\n";
    } else
    {
      const struct_typet::componentt &comp=comps[comp_index];
      if (!is_class_name_comp(comp, comp_index))
      {
        indent(result, 2u)+="com.diffblue.java_testcase.Reflector.setInstanceField(";
        result+=this_name;
        result+=",\"";
        result+=id2string(comp.get_pretty_name());
        result+="\",";
        ref_factory.add_value(result, st, value);
        result+=")";
        if (comp_index < comps.size() - 1) result+=";\n";
      }
    }
    ++comp_index;
  }
};

void reference_factoryt::add_value(std::string &result, const symbol_tablet &st,
    const struct_exprt &value, const std::string &this_name)
{
  const namespacet ns(st);
  const typet &type=value.type();

  std::string qualified_class_name;
  add_qualified_class_name(qualified_class_name, ns, type);  

  std::string instance_expr;
  bool should_mock = mock_classes.count(qualified_class_name);
  if(should_mock)
    instance_expr = mockenv_builder.instantiate_mock(qualified_class_name, false);
  else
    instance_expr = "com.diffblue.java_testcase.Reflector.forceInstance(\"" + qualified_class_name + "\")";
      
  result+='(' + qualified_class_name + ") " + instance_expr + ";\n";

  if(should_mock)
    result+=mockenv_builder.register_mock_instance(qualified_class_name, this_name);

  member_factoryt mem_fac(result, st, this_name, type, *this);
  const struct_exprt::operandst &ops=value.operands();
  std::for_each(ops.begin(), ops.end(), mem_fac);
}

void reference_factoryt::add_assign_value(std::string &result, const symbol_tablet &st,
    const symbolt &symbol, const exprt &value)
{
  std::string symbol_name;
  add_symbol(symbol_name, symbol);
  result+=symbol_name;
  result+='=';
  add_value(result, st, value, symbol_name);
  result+=";\n";
}

bool is_input_struct(const symbolt &symbol)
{
  return std::string::npos != id2string(symbol.name).find("tmp_object_factory");
}

void reference_factoryt::add_global_state_assignments(std::string &result, const symbol_tablet &st,
    inputst &in)
{
  for (inputst::const_reverse_iterator it=in.rbegin(); it != in.rend(); ++it)
  {
    const symbolt &symbol=st.lookup(it->first);
    if (!symbol.is_static_lifetime) continue;
    indent(result, 2u);
    if (is_input_struct(symbol)) add_decl_with_init_prefix(result, st, symbol);
    add_assign_value(result, st, symbol, it->second);
  }
}

std::set<irep_idt> get_parameters(const symbolt &func)
{
  std::set<irep_idt> result;
  const code_typet &code_type=to_code_type(func.type);
  const code_typet::parameterst &params=code_type.parameters();
  for (const code_typet::parametert &param : params)
    result.insert(param.get_identifier());
  return result;
}

  bool reference_factoryt::add_func_call_parameters(std::string &result, const symbol_tablet &st,
    const irep_idt &func_id, inputst &inputs)
{
  const symbolt &func=st.lookup(func_id);
  const std::set<irep_idt> params(get_parameters(func));
  for (const irep_idt &param : params)
  {
    const symbolt &symbol=st.lookup(param);
    const inputst::iterator value=inputs.find(param);
    if(inputs.end()==value) 
    {
      return false;
    }
    else
    {
      add_decl_with_init_prefix(indent(result, 2u), st, symbol);
      add_assign_value(result, st, symbol, value->second);
    }
  }
  return true;
}

std::string symbol_to_function_name(const symbolt &s) {

  const std::string func_name_with_brackets(id2string(s.pretty_name));
  const size_t sz=func_name_with_brackets.size();
  assert(sz >= 2u);
  return func_name_with_brackets.substr(0, sz - 2);

}
  
void add_func_call(std::string &result, const symbol_tablet &st,
    const irep_idt &func_id)
{
  // XXX: Should be expr2java(...) once functional.
  const symbolt &s=st.lookup(func_id);
  indent(result, 2u) += symbol_to_function_name(s);
  result+='(';
  const std::set<irep_idt> params(get_parameters(s));
  unsigned nparams = 0;
  for (const irep_idt &param : params)
  {
    if(nparams++ != 0)
      result+=", ";
    add_symbol(result, st.lookup(param));
  }
  result+=");\n";
}

std::string get_escaped_func_name(const symbolt &symbol)
{
  std::string result(id2string(symbol.pretty_name));
  substitute(result, ".", "_");
  substitute(result, "(", "X");
  substitute(result, ")", "Y");
  return result;
}

bool shouldnt_mock_class(const std::string& classname)
{
  // Should make a proper black/whitelist in due time; for now just avoid
  // mocking things like Exceptions.
  return classname.find("java.") == 0;
}

const symbolt& get_or_fake_symbol(const symbol_tablet& st, const irep_idt& id,
  const typet& expected_type, symbolt& fake_symbol)
{

  auto findit=st.symbols.find(id);

  if(findit==st.symbols.end())
  {
    // Dynamic object names are not in the symtab at the moment.
    fake_symbol.type=expected_type;
    fake_symbol.name=id;
    std::string namestr=as_string(id);
    size_t findidx=namestr.find("::");
    if(findidx==std::string::npos)
      fake_symbol.base_name=fake_symbol.name;
    else
    {
      assert(namestr.size() >= findidx + 3);
      fake_symbol.base_name=namestr.substr(findidx + 2);
    }
    return fake_symbol;
  }
  else
    return findit->second;

}

void string_to_statements(const std::string& instring,
			  std::vector<init_statement>& out)
{
  // Break the declaration into lines, for formatting purposes.
  // (Todo: gather the init code this way everywhere, instead of as a long string)
  for(size_t last_semi=0, this_semi=instring.find(';', 1);
      last_semi!=std::string::npos;
      last_semi=this_semi, this_semi=instring.find(';', last_semi+1))
  {
    size_t takefrom=last_semi + 1;
    while(takefrom < this_semi &&
	  takefrom < instring.length() &&
	  isspace(instring[takefrom]))
      ++takefrom;
	    
    if(takefrom < this_semi && takefrom < instring.length())
    {
      std::string thisline=instring.substr(
	takefrom, this_semi==std::string::npos ? std::string::npos : this_semi - takefrom);
      out.push_back(init_statement::statement(thisline));
    }
  }
}

struct java_call_descriptor {
  std::string classname;
  std::string funcname;
  code_typet original_type;
  std::vector<java_type> java_arg_types;
  java_type java_ret_type;
};

void populate_descriptor_names(const symbolt& func, java_call_descriptor& desc)
{
  auto class_and_function_name=symbol_to_function_name(func);
  size_t sepidx=class_and_function_name.rfind('.');
  assert(sepidx!=std::string::npos && "Unqualified call in Java code?");
  desc.classname=class_and_function_name.substr(0, sepidx);
  desc.funcname=class_and_function_name.substr(sepidx + 1);
}

void populate_descriptor_types(const symbolt& func, const typet& ret_type,
  java_call_descriptor& desc, const symbol_tablet& st)
{
  const code_typet &code_type=to_code_type(func.type);
  desc.original_type=code_type;
 
  for(auto &param : code_type.parameters())
  {
    std::string thisparam;
    bool type_is_primitive;
    // Skip implicit 'this' parameter
    if(param.get_this())
      continue;
    add_decl_from_type(thisparam,st,param.type(),&type_is_primitive);
    desc.java_arg_types.push_back({thisparam,type_is_primitive});
  }

  add_decl_from_type(desc.java_ret_type.classname,st,
		     ret_type,&desc.java_ret_type.is_primitive);
}
  
void reference_factoryt::add_mock_call(
  const interpretert::function_assignments_contextt defined_symbols_context,
  const java_call_descriptor& desc,
  const symbol_tablet& st)
{

  const auto& defined_symbols=defined_symbols_context.assignments;
  std::string return_value;
  assert(defined_symbols.size()!=0);
      
  if(desc.java_ret_type.is_primitive)
  {
    // defined_symbols should be simply [ some_identifier = some_primitive ]
    assert(defined_symbols.size()==1);
    add_value(return_value,st,defined_symbols.back().value);
  }
  else
  {
    // defined_symbols may be something like [ id1 = { x = 1, y = "Hello" },
    //                                         id2 = { a = id1, b = "World" } ]
    std::vector<init_statement> init_statements;

    std::ostringstream mocknameoss;
    static unsigned mocknumber=0;
    mocknameoss << "mock_instance_" << (++mocknumber);
    std::string mockname=mocknameoss.str();
    init_statements.push_back(
      init_statement::statement(desc.java_ret_type.classname + " " + mockname));

    // Start an anonymous scope, as the symbol names defined below may not be unique
    // if the same method stub was used more than once.
    init_statements.push_back(init_statement::scopeOpen());
	
    for(auto defined : defined_symbols)
    {
      symbolt fake_symbol;
      const symbolt& use_symbol=get_or_fake_symbol(st, defined.id,
				  defined.value.type(), fake_symbol);

      // Initial empty statement makes the loop below easier.
      std::string this_object_init=";"; 
      add_decl_with_init_prefix(this_object_init, st, use_symbol);
      add_assign_value(this_object_init, st, use_symbol, defined.value);

      string_to_statements(this_object_init, init_statements);
    }

    const irep_idt& last_sym_name=defined_symbols.back().id;
    init_statements.push_back(
      init_statement::statement(mockname + "=" + as_string(last_sym_name)));

    // End anonymous scope.
    init_statements.push_back(init_statement::scopeClose());
	
    return_value=as_string(mockname);
	  
    mockenv_builder.add_to_prelude(init_statements);
  }

  bool is_static=!desc.original_type.has_this();
  bool is_constructor=desc.original_type.get_bool(ID_constructor);
      
  if(is_static)
    mockenv_builder.static_call(desc.classname, desc.funcname, desc.java_arg_types, return_value);
  else if(is_constructor)
  {
    std::string caller=as_string(defined_symbols_context.calling_function);
    size_t namespace_idx=caller.find("java::");
    size_t classname_idx=namespace_idx + 6;
    size_t method_idx=caller.rfind('.');
    assert(namespace_idx==0 && method_idx!=std::string::npos);
    mockenv_builder.constructor_call(caller.substr(classname_idx, method_idx - classname_idx),
				     desc.classname, desc.java_arg_types, return_value);
  }
  else
    mockenv_builder.instance_call(desc.classname, desc.funcname,
      desc.java_arg_types, desc.java_ret_type, return_value);

}
  
void reference_factoryt::add_mock_objects(const symbol_tablet &st,
  const interpretert::list_input_varst& opaque_function_returns)
{

  mock_classes.clear();

  for(auto fn_and_returns : opaque_function_returns)
  {

    const symbolt &func=st.lookup(fn_and_returns.first);    
    struct java_call_descriptor desc;
    populate_descriptor_names(func,desc);

    if(shouldnt_mock_class(desc.classname))
      continue;

    // Note that this class must be mocked whenever we try to generate a reference to it:
    mock_classes.insert(desc.classname);

    assert(fn_and_returns.second.size() != 0);
    // Get type from replacement value,
    // as remove_returns passlet has scrubbed the function return type by this point.
    const auto& last_definition_list=fn_and_returns.second.back().assignments;
    const auto& last_toplevel_assignment=last_definition_list.back().value;
    
    populate_descriptor_types(func,last_toplevel_assignment.type(),desc,st);

    for(auto defined_symbols_context : fn_and_returns.second)
      add_mock_call(defined_symbols_context,desc,st);
      
  }

}

} // End of anonymous namespace

std::string generate_java_test_case_from_inputs(const symbol_tablet &st, const irep_idt &func_id, inputst inputs, const interpretert::list_input_varst& opaque_function_returns, bool disable_mocks)
{
  const symbolt &func=st.lookup(func_id);
  const std::string func_name(get_escaped_func_name(func));
  std::string result;

  // Do this first since the mock object creation can require annotations on the test class.
  // Parameter is the indent level on generated code.
  reference_factoryt ref_factory(4);

  if(!disable_mocks)
    ref_factory.add_mock_objects(st, opaque_function_returns);

  result += ref_factory.mockenv_builder.get_class_annotations() + "\n";
  add_test_class_name(result, func_name);

  std::string post_mock_setup_result;
  
  ref_factory.add_global_state_assignments(post_mock_setup_result, st, inputs);
  bool exists_func_call = ref_factory.add_func_call_parameters(post_mock_setup_result, st, func_id, inputs);
  // Finalise happens here because add_func_call_parameters et al
  // may have generated mock objects.
  std::string mock_final = ref_factory.mockenv_builder.finalise_instance_calls();
  result += "\n" + ref_factory.mockenv_builder.get_mock_prelude() +
    "\n\n" + post_mock_setup_result + "\n\n" + mock_final;
  if(exists_func_call)
  {
    add_func_call(result,st,func_id);
  }

  indent(result)+="}\n";
  return result+="}\n";

}

std::string func_name(const symbolt &symbol)
{
  return get_escaped_func_name(symbol);
}
