/*******************************************************************\

Module: Uncaught Exceptions

Author: Peter Schrammel

\*******************************************************************/

#ifndef CPROVER_UNCAUGHT_EXCEPTIONS_H
#define CPROVER_UNCAUGHT_EXCEPTIONS_H

#include <iostream>

#include <goto-programs/goto_functions.h>
#include <analyses/call_graph.h>
#include <util/ui_message.h>
#include <util/xml.h>

class uncaught_exceptionst
{
public:

  explicit uncaught_exceptionst(const namespacet &_ns,
				const goto_functionst &_goto_functions)
    :
    ns(_ns),
    goto_functions(_goto_functions),
    call_graph(_goto_functions)
  {
    
  }


  class domaint
  {
  public:
    typedef std::set<irep_idt> exception_typest;
    typedef std::set<source_locationt> locationst;
    typedef std::map<locationst,exception_typest> valuet;

    static const source_locationt top_location;
    static const std::string top_exception_type;

    domaint() {}
    
    domaint(goto_programt::const_targett _t,
	    bool locations_top=false, bool exceptions_top=false);
     
    inline const valuet &get() const { return value; }

    void meetc(const domaint& e);
    void join(const domaint& e);
    bool contained(const domaint& e);
    void reduce();

  protected:
    valuet value;
    
    bool has_top_exception_type();
    bool has_top_location();

    template<class T> void set_intersect(std::set<T> &s1,
					 const std::set<T> &s2);
    template<class T> void set_diff(std::set<T> &s1,
				    const std::set<T> &s2);
    template<class T> bool set_nonempty_intersection(
      const std::set<T> &s1,
      const std::set<T> &s2);
    template<class T> bool set_equals(const std::set<T> &s1,
				      const std::set<T> &s2);
    template<class T> bool set_contained(const std::set<T> &s1,
					 const std::set<T> &s2);

    irep_idt cleanup(irep_idt t);
  };
  
  typedef std::map<irep_idt,domaint> function_exception_mapt; 
    
  inline void operator()(function_exception_mapt &exceptions);

  static void output(std::ostream &out,
		     const domaint &d);
  static void output(std::ostream &out,
		     const function_exception_mapt &exceptions);
  static void xml_output(xmlt &xml, 
			 const domaint &d);
  static void xml_output(std::ostream &out,
			 const function_exception_mapt &exceptions);

 protected:
  const namespacet &ns;
  const goto_functionst &goto_functions;
  const call_grapht call_graph;

  void analyze_function(std::set<irep_idt> &new_worklist,
			function_exception_mapt &exceptions,
			const irep_idt &function_name);

  void get_virtual_methods(const exprt &function_expr,
			std::set<irep_idt> &method_names) const;

  bool is_unknown_function(const irep_idt &function_name) const;
};

void show_uncaught_exceptions(
  ui_message_handlert::uit ui,
  const class symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  std::ostream &out);

#endif
