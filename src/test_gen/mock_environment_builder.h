
#include <vector>
#include <unordered_map>
#include <set>
#include <sstream>
#include <functional> // for std::hash

// Supporting types for the map tracking instance method interception

struct method_signature {
  
  const std::string classname;
  const std::string methodname;
  const std::vector<std::string> argtypes;

  method_signature() = default;
  
method_signature(const std::string& cn, const std::string& mn, const std::vector<std::string> ats) :
  classname(cn), methodname(mn), argtypes(ats) {}

  bool operator==(const method_signature& other) const {
    return other.classname == classname && other.methodname == methodname && other.argtypes == argtypes;
  }

};

namespace std {
  template<> struct hash<method_signature> {

    size_t operator()(const method_signature& m) const {

      size_t ret = hash<string>()(m.classname) ^
	hash<string>()(m.methodname);

      for(auto iter : m.argtypes)
	ret ^= hash<string>()(iter);

      return ret;

    }
  
  };
}

struct instance_method_answer {

  std::string answer_object;
  std::string answer_list;

  instance_method_answer() = default;
  
instance_method_answer(const std::string& ao, const std::string& al) :
  answer_object(ao), answer_list(al) {}
  
};

class mock_environment_builder {

  // Count how many fresh instances we've produced of each typename, to generate fresh names.
  std::unordered_map<std::string, unsigned long> name_counter;

  // Track class instance methods that have an answer object set up.
  std::unordered_map<method_signature, instance_method_answer> instance_method_answers;

  // Build up a set of classes that need PowerMock setup (those whose constructors and/or static methods we need to intercept)
  std::set<std::string> powermock_classes;

  // Accumulate mock object setup statements that will precede the test case entry point
  std::ostringstream mock_prelude;

  // Newline character plus indenting for the prelude:
  std::string prelude_newline;
  
 public:

  mock_environment_builder(unsigned int ip);
  
  // Generate mock setup code for a fresh instance of 'tyname'; return a unique local name for it.
  std::string get_fresh_instance(const std::string& tyname, bool is_constructor);

  // Intercept the next instance call to targetobj.methodname(paramtype0, paramtype1, ...) and return retval.
  void instance_call(const std::string& targetclass, const std::string& methodname, const std::vector<std::string>& argtypes, const std::string& rettype, const std::string& retval);

  // Write instance method interception code that can only be generated once all required intercepts are known.
  void finalise_instance_calls();
  
  // Intercept the next static call to targetclass.methodname(argtypes...) and return retval.
  void static_call(const std::string& targetclass, const std::string& methodname, const std::vector<std::string>& argtypes, const std::string& retval);

  // Return annotations needed for the main class to run under JUnit:
  std::string get_class_annotations();

  // Return the mock setup code that should directly precede the test entry point.
  std::string get_mock_prelude() { return mock_prelude.str(); }
  
};
