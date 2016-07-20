
#include "mock_environment_builder.h"

#include <iostream>
#include <locale>
#include <assert.h>

mock_environment_builder::mock_environment_builder(unsigned int ip) {

  prelude_newline = '\n';
  for(unsigned int i = 0; i < ip; ++i)
    prelude_newline += ' ';
  mock_prelude << prelude_newline;

}

std::string mock_environment_builder::register_mock_instance(const std::string& tyname, const std::string& instancename) {

  std::string instanceList = tyname + "_instances";
  if(mock_instances_exist.insert(tyname).second)
    mock_prelude << "java.util.ArrayList<" << tyname << "> " << instanceList << " = new java.util.ArrayList<" << tyname << ">();" << prelude_newline;
  return prelude_newline + instanceList + ".add(" + instancename + ");";

}

// Create a fresh mock instance.
std::string mock_environment_builder::instantiate_mock(const std::string& tyname, bool is_constructor) {

  return "org.mockito.Mockito.mock(" + tyname + ".class);";

}

// Return retval the next time a targetclass is constructed.
// We don't use argtypes at the moment.
void mock_environment_builder::constructor_call(const std::string& callingclass, const std::string& targetclass, const std::vector<std::string>& argtypes, const std::string& retval) {

  // Note that the *caller* (not the callee) needs PrepareForTest.
  powermock_classes.insert(callingclass);
  
  mock_prelude <<
    "org.powermock.api.mockito.PowerMockito.whenNew(" << targetclass << ".class).withAnyArguments().thenReturn(" << retval << ");" << prelude_newline;

}


static std::string classname_to_symname(const std::string& classname) {

  std::string ret = classname;
  for(size_t i = 0, ilim = classname.length(); i != ilim; ++i)
    if(ret[i] == '.')
      ret[i] = '_';
  return ret;

}

static std::string box_java_type(const std::string& unboxed) {

  if(unboxed == "boolean")
    return "Boolean";
  else if(unboxed == "byte")
    return "Byte";
  else if(unboxed == "char")
    return "Character";
  else if(unboxed == "float")
    return "Float";
  else if(unboxed == "int")
    return "Integer";
  else if(unboxed == "long")
    return "Long";
  else if(unboxed == "short")
    return "Short";
  else if(unboxed == "double")
    return "Double";
  else
    return unboxed;

}

// Intercept the next instance call to targetclass::methodname(paramtype0, paramtype1, ...) and return retval.
// At the moment we don't care which instance of targetclass was called against.
void mock_environment_builder::instance_call(const std::string& targetclass, const std::string& methodname, const std::vector<std::string>& argtypes, const std::string& rettype, const std::string& retval) {

  method_signature sig(targetclass, methodname, argtypes);
  instance_method_answer dummy_ans;
  
  auto insertresult = instance_method_answers.insert(std::make_pair(sig, dummy_ans));

  if(insertresult.second) {

    // This is the first interception of targetclass::methodname (for this overload).
    // Set up a response list and answer object:

    std::ostringstream answerlist;
    answerlist << classname_to_symname(targetclass) << "_" << methodname;
    for(auto iter : argtypes)
      answerlist << "_" << iter;

    std::string al = answerlist.str();
    std::string ao = answerlist.str();
    al += "_answer_list";
    ao += "_answer_object";

    insertresult.first->second = instance_method_answer(ao, al);

    std::string boxed_type = box_java_type(rettype);
    
    mock_prelude << "final java.util.ArrayList<" << boxed_type << "> " << al << " = new java.util.ArrayList<" << boxed_type << ">();" << prelude_newline <<
      "final com.diffblue.java_testcase.IterAnswer " << ao << " = new com.diffblue.java_testcase.IterAnswer<" << boxed_type << ">(" << al << ");" << prelude_newline;
    
  }

  // Add the desired return value to the list:
  auto found = insertresult.first->second;
  mock_prelude << found.answer_list << ".add(" << retval << ");" << prelude_newline;
  
}

static std::locale loc;
static const char* prefix = "__primitive__";
static unsigned int prefixlen = std::string(prefix).length();

static void generate_arg_matchers(std::ostringstream& printto, const std::string& targetclass, const std::string& methodname, const std::vector<std::string>& argtypes) {

  printto << "org.mockito.Mockito.when(" << targetclass << "." << methodname << "(";
  
  for(unsigned int i = 0, ilim = argtypes.size(); i < ilim; ++i) {
    
    const std::string& arg = argtypes[i];
    if(i != 0)
      printto << ", ";

    // Accept anyInt, anyShort, anyDouble, etc for primitives, or isA to match object types.
    
    if(!arg.substr(0, prefixlen).compare(prefix))
      printto << "org.mockito.Matchers.any" << (char)toupper(arg[prefixlen]) << arg.substr(prefixlen + 1) << "()";
    else
      printto << "org.mockito.Matchers.isA(" << arg << ".class)";

  }

  printto << "))";

}

std::string mock_environment_builder::finalise_instance_calls() {

  // We've created a number of mock objects of various types. Hook them up to their type-global
  // list of function return values.

  std::ostringstream result;
  result << prelude_newline;
  
  for(auto iter : instance_method_answers) {
    
    const auto& cname = iter.first.classname;
    if(!mock_instances_exist.count(cname)) {
      std::cout << "Warning: class " << cname << " has instance method mocks but never instantiated\n";
    }

    std::string instanceList = cname + "_instances";
    std::string instanceIter = cname + "_iter";
    
    result << "for(" << cname << " " << instanceIter << " : " << instanceList << ')' << prelude_newline << "  ";
    generate_arg_matchers(result, instanceIter, iter.first.methodname, iter.first.argtypes);
    result << ".thenAnswer(" << iter.second.answer_object << ");" << prelude_newline;

  }

  return result.str();

}

// Intercept the next static call to targetclass.methodname(argtypes...) and return retval.
void mock_environment_builder::static_call(const std::string& targetclass, const std::string& methodname, const std::vector<std::string>& argtypes, const std::string& retval) {

  // Intercepting static calls needs PowerMockito setup:
  auto inserted = powermock_classes.insert(targetclass);
  // Call mockStatic the first time a particular type is needed:
  if(inserted.second)
    mock_prelude << "org.powermock.api.mockito.PowerMockito.mockStatic(" << targetclass << ".class);" << prelude_newline;

  generate_arg_matchers(mock_prelude, targetclass, methodname, argtypes);

  mock_prelude << ".thenReturn(" << retval << ");" << prelude_newline;
  
}

// Return annotations needed for the main class to run under JUnit:
std::string mock_environment_builder::get_class_annotations() {

  if(powermock_classes.size() == 0)
    return "";
  
  std::ostringstream out;
  out << "@org.junit.runner.RunWith(org.powermock.modules.junit4.PowerMockRunner.class)\n";
  out << "@org.powermock.core.classloader.annotations.PrepareForTest( { ";

  for(std::set<std::string>::iterator it = powermock_classes.begin(), itend = powermock_classes.end(); it != itend; ++it) {
    if(it != powermock_classes.begin())
      out << ", ";
    out << *it << ".class";
  }

  out << " } )";

  return out.str();
  
}

void mock_environment_builder::add_to_prelude(const std::vector<init_statement>& statements) {

  for(const auto& s : statements)
  {
    switch(s.type)
    {
    case init_statement::SCOPE_OPEN:
      mock_prelude << '{';
      prelude_newline += "  ";
      mock_prelude << prelude_newline;      
      break;
    case init_statement::SCOPE_CLOSE:
      mock_prelude << "\b\b";
      if(prelude_newline.length() >= 3)
	prelude_newline.erase(prelude_newline.length() - 2, 2);
      mock_prelude << '}' << prelude_newline;
      break;
    case init_statement::STATEMENT:
      mock_prelude << s.statementText << ';' << prelude_newline;
    }
  }
    
}
