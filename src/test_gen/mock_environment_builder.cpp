
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

// Intercept the next constructor call to tyname and return a fresh mock instance.
std::string mock_environment_builder::get_fresh_instance(const std::string& tyname, bool is_constructor) {

  // Make a fresh local name for this instance:
  unsigned long count = ++(name_counter[tyname]);
  std::string freshname;
  {
    std::ostringstream freshname_oss;
    freshname_oss << "mock_" << tyname << "_" << count;
    freshname = freshname_oss.str();
  }

  if(is_constructor) {
    
    // Note that constructor interception needs setting up:
    powermock_classes.insert(tyname);

  }

  mock_prelude << tyname << " " << freshname << " = " << "org.mockito.Mockito.mock(" + tyname + ".class);" << prelude_newline;
  
  if(is_constructor) {

    // Intercept the next constructor call and return this:
    mock_prelude <<
      "org.powermock.api.mockito.PowerMockito.whenNew(" << tyname << ".class).withAnyArguments().thenReturn(" << freshname << ");" << prelude_newline;

  }

  return freshname;
  
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
      "final IterAnswer " << ao << " = new IterAnswer<" << boxed_type << ">(" << al << ");" << prelude_newline;
    
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

void mock_environment_builder::finalise_instance_calls() {

  // We've created a number of mock objects of various types. Hook them up to their type-global
  // list of function return values.

  for(auto iter : instance_method_answers) {

    unsigned long count = name_counter[iter.first.classname];
    if(count == 0) {
      std::cout << "Warning: class " << iter.first.classname << " has instance method mocks but never instantiated\n";
    }

    for(unsigned long i = 1; i <= count; ++i) {

      std::ostringstream namestr;
      namestr << "mock_" << iter.first.classname << "_" << i;
      std::string name = namestr.str();

      generate_arg_matchers(mock_prelude, name, iter.first.methodname, iter.first.argtypes);

      mock_prelude << ".thenAnswer(" << iter.second.answer_object << ");" << prelude_newline;

    }

  }

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
