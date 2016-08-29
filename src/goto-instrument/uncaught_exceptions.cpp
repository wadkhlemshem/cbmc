/*******************************************************************\

Module: Uncaught Exceptions

Author: Peter Schrammel

\*******************************************************************/

#include <iostream>

#include <util/std_expr.h>
#include <util/prefix.h>

#include "uncaught_exceptions.h"


const source_locationt uncaught_exceptionst::domaint::top_location =
  source_locationt();
const std::string uncaught_exceptionst::domaint::top_exception_type =
  "__CPROVER_all_exceptions";

/*******************************************************************\

Function: uncaught_exceptionst::domaint::domaint

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

uncaught_exceptionst::domaint::domaint(goto_programt::const_targett _t,
				       bool locations_top, 
				       bool exceptions_top)
{
  locationst locations;
  if(locations_top) locations.insert(top_location);
  else locations.insert(_t->source_location);
  exception_typest &exception_types = value[locations];
  if(locations_top && !exceptions_top) //catch
  {
    const irept &elist = _t->code.find(ID_exception_list);
    forall_irep(it, elist.get_sub())
    {
      if(it->id()=="")  // catch(...)
      {
	exception_types.clear();
	exception_types.insert(top_exception_type);
	break;
      }
      exception_types.insert(cleanup(it->id()));
    }
  }
  else if(!locations_top && exceptions_top) //unknown function call
  {
    exception_types.clear();
    exception_types.insert(top_exception_type);
  }
  else //throw
  {
    const irept &elist = _t->code.op0().find(ID_exception_list);
    forall_irep(it, elist.get_sub())
    {
      exception_types.insert(cleanup(it->id()));
    }
  }
}

/*******************************************************************\

Function: uncaught_exceptionst::analyze_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uncaught_exceptionst::analyze_function(std::set<irep_idt> &new_worklist,
					    function_exception_mapt &exceptions,
					    const irep_idt &function_name)
{
#ifdef DEBUG
  std::cout << "Analyzing function " << function_name << std::endl;
#endif

  const goto_programt &body=goto_functions.function_map.at(function_name).body;
  std::list<domaint> thrown, caught;
  thrown.push_back(domaint());
  
  forall_goto_program_instructions(i_it, body)
  {
    if(i_it->is_catch())
    {
      if(!i_it->targets.empty()) //CATCH-PUSH
      {
#if 0
	std::cout << "push" << std::endl;
#endif
        thrown.push_back(domaint());
	caught.push_back(domaint(i_it,true));
      }
      else //CATCH-POP
      {
#if 0
	std::cout << "pop" << std::endl;
	std::cout << "thrown: " << std::endl; output(std::cout,thrown.back());
	std::cout << "caught: " << std::endl; output(std::cout,caught.back());
#endif
	thrown.back().meetc(caught.back());
#if 0
	std::cout << "meetc: " << std::endl; output(std::cout,thrown.back());
#endif
	(--(--thrown.end()))->join(thrown.back());
	thrown.pop_back();
#if 0
	std::cout << "join: " << std::endl; output(std::cout,thrown.back());
#endif
	caught.pop_back();
      }
    }
    if(i_it->is_throw())
    {
#if 0
      std::cout << "throw" << std::endl;
#endif
      domaint d(i_it);
      thrown.back().join(d);
    }
    if(i_it->is_function_call())
    {
      const exprt &function_expr=to_code_function_call(i_it->code).function();
      if(function_expr.id()==ID_symbol) //function/method call
      {
	const irep_idt &fname = to_symbol_expr(function_expr).get_identifier();
#ifdef DEBUG
        std::cout << "call to " << fname << std::endl;
#endif
        if(!is_unknown_function(fname))
          thrown.back().join(exceptions[fname]);
	else //unknown function call
          thrown.back().join(domaint(i_it,false,true));
      }
      else //virtual method call 
      {
	//this overapproximates the virtual function calls 
        //  by joining the exceptions of all virtual methods
        //  in all subclasses
	std::set<irep_idt> method_names;
	get_virtual_methods(function_expr,method_names);
	for(std::set<irep_idt>::iterator it = method_names.begin();
	    it != method_names.end(); ++it)
	{
#ifdef DEBUG
          std::cout << "virtual call to " << *it << std::endl;
#endif
	  if(!is_unknown_function(*it))
	    thrown.back().join(exceptions[*it]);
	  else //unknown function call
	    thrown.back().join(domaint(i_it,false,true));
	}
      }
#if 0
      std::cout << ":" << std::endl; output(std::cout,thrown.back());
#endif
    }
  }

#if 0
  std::cout << "end of function: " << std::endl; 
  output(std::cout,thrown.back());
#endif

  //if changed, add all predecessors in the call graph to the new worklist
  assert(thrown.size()==1);
  if(!thrown.back().contained(exceptions[function_name]))
  {
    exceptions[function_name] = thrown.back();
    for(call_grapht::grapht::const_iterator g_it = call_graph.graph.begin();
	g_it != call_graph.graph.end(); ++g_it)
    {
      if(g_it->second==function_name)
	new_worklist.insert(g_it->first);
    }
  }
}

/*******************************************************************\

Function: uncaught_exceptionst::get_virtual_methods

  Inputs:

 Outputs:

 Purpose: get matching virtual method names of all subclasses

\*******************************************************************/

void uncaught_exceptionst::get_virtual_methods(const exprt &function_expr,
  std::set<irep_idt> &method_names) const
{
#if 0
  std::cout << "METHOD CALL: " << function_expr << std::endl;
#endif

  dereference_exprt deref = to_dereference_expr(function_expr);
  member_exprt member = to_member_expr(deref.pointer());
  irep_idt method_name = member.get_component_name();

#if 0
  std::cout << "METHOD EXPR: " << method_name << std::endl;
#endif

  //extract type and name
  std::string method_str = id2string(method_name);
  method_str = method_str.substr(15); //strip off virtual_table::
  size_t pos = method_str.find_last_of("::");
  irep_idt method_name_suffix = method_str.substr(pos+1);
  irep_idt method_type = method_str.substr(0,pos-1);

#if 0
  std::cout << "METHOD TYPE EXPR: " << method_type << std::endl;
  std::cout << "METHOD NAME: " << method_name_suffix << std::endl;
#endif

  // find reflexive and transitive subclasses of the class
  std::set<irep_idt> sub_classes;
  sub_classes.insert(method_type); //include class itself
  bool change = true;
  while(change)
  {
    change = false;
    forall_symbols(it, ns.get_symbol_table().symbols)
    {
      if(it->second.type.id()==ID_struct)
      {
	for(std::set<irep_idt>::iterator s_it = sub_classes.begin();
	    s_it != sub_classes.end(); ++s_it)
	{
	  if(to_class_type(it->second.type).has_base(*s_it))
	  {
	    change = change || sub_classes.insert(it->first).second;
	  }
	}
      }
    }
  }

#if 0
  for(std::set<irep_idt>::iterator it = sub_classes.begin();
      it != sub_classes.end(); ++it)
    std::cout << "  SUBCLASS: " << *it << std::endl;
#endif

  //collect virtual method names from symbol table
  for(std::set<irep_idt>::iterator it = sub_classes.begin();
	it != sub_classes.end(); ++it)
  {
    const symbolt *s;
    if(!ns.lookup(*it,s))
    {
      const struct_union_typet::componentst &methods = 
	to_class_type(s->type).methods();
      for(struct_union_typet::componentst::const_iterator 
	    m_it = methods.begin();
	  m_it != methods.end(); ++m_it)
      {
	irep_idt virtual_name = m_it->get("virtual_name");
	if(virtual_name == method_name_suffix) 
          method_names.insert(id2string(m_it->get_name()));
      }
    }
  }
}

/*******************************************************************\

Function: uncaught_exceptionst::operator()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uncaught_exceptionst::operator()(function_exception_mapt &exceptions)
{
  std::set<irep_idt> worklist, new_worklist;
  forall_goto_functions(f_it, goto_functions)
    worklist.insert(f_it->first);
  while(!worklist.empty())
  {
    new_worklist.clear();
    //ensure a fair iteration strategy (simply iterate before updating)
    for(std::set<irep_idt>::const_iterator f_it =
	  worklist.begin();
	f_it!=worklist.end(); ++f_it)
    {
      analyze_function(new_worklist,exceptions,*f_it);
    }

    //update worklist
    worklist.clear();
    worklist.insert(new_worklist.begin(),new_worklist.end());
  }
}

/*******************************************************************\

Function: uncaught_exceptionst::domaint::meetc()

  Inputs:

 Outputs:

 Purpose: meet with the complement of the rhs argument

\*******************************************************************/

void uncaught_exceptionst::domaint::meetc(const domaint& e)
{
  valuet old_value = value;
  value.clear();
  for(valuet::const_iterator it1 = old_value.begin();
      it1!=old_value.end(); ++it1)
  {
    for(valuet::const_iterator it2 = e.value.begin();
      it2!=e.value.end(); ++it2)
    {
      // ensure that rhs argument has top location
      assert(it2->first.size()==1 && *it2->first.begin()==top_location);
      // rhs argument has top exception type
      if(it2->second.size()==1 && *it2->second.begin()==top_exception_type)
	continue;
      if(!set_nonempty_intersection(it1->second,it2->second))
  	value[it1->first] = it1->second;
    }    
  }
  reduce();
}

/*******************************************************************\

Function: uncaught_exceptionst::domaint::join()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uncaught_exceptionst::domaint::join(const domaint& e)
{
  value.insert(e.value.begin(),e.value.end());
  reduce();
}

/*******************************************************************\

Function: uncaught_exceptionst::domaint::contained()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool uncaught_exceptionst::domaint::contained(const domaint& e)
{
  for(valuet::iterator it1 = value.begin();
      it1!=value.end(); ++it1)
  {
    bool contained = false;
    for(valuet::const_iterator it2 = e.value.begin();
      it2!=e.value.end(); ++it2)
    {
      if(set_contained(it1->first,it2->first) &&
	 set_equals(it1->second,it2->second))
      {
	contained = true;
	break;
      }
    }
    if(!contained) return false;
  }
  return true;
}

/*******************************************************************\

Function: uncaught_exceptionst::domaint::reduce()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uncaught_exceptionst::domaint::reduce()
{
  //remove empty
  valuet::iterator it = value.begin();
  while(it!=value.end())
  {
    if(it->first.empty() || it->second.empty())
      value.erase(it++);
    else ++it;
  }
  //merge
  for(valuet::iterator it1 = value.begin();
      it1!=value.end(); ++it1)
  {
    valuet::iterator it2 = it1; ++it2;
    for(; it2!=value.end(); ++it2)
    {
      if(set_equals(it1->second,it2->second))
      {
	locationst u = it1->first;
	u.insert(it2->first.begin(),it2->first.end());
	value[u] = it1->second;
      }
    }    
  }
  //remove subsumed
  valuet old_value = value;
  value.clear();
  for(valuet::const_iterator it1 = old_value.begin();
      it1!=old_value.end(); ++it1)
  {
    bool subsumed = false;
    for(valuet::const_iterator it2 = old_value.begin();
	it2!=old_value.end(); ++it2)
    {
      if(it1!=it2 &&
	 set_contained(it1->first,it2->first) &&
	 set_equals(it1->second,it2->second))
      {
	subsumed = true;
	break;
      }
    }
    if(!subsumed) value.insert(*it1);
  }
}

/*******************************************************************\

Function: uncaught_exceptionst::domaint::set_intersect()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T> void uncaught_exceptionst::domaint::set_intersect(
						     std::set<T> &s1,
						     const std::set<T> &s2)
{
  typename std::set<T>::iterator it = s1.begin();
  while(it!=s1.end())
  {
    if(s2.find(*it)==s2.end())
      s1.erase(it++);
    else ++it;
  } 
}

/*******************************************************************\

Function: uncaught_exceptionst::domaint::set_diff()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T> void uncaught_exceptionst::domaint::set_diff(
						     std::set<T> &s1,
						     const std::set<T> &s2)
{
  typename std::set<T>::iterator it = s1.begin();
  while(it!=s1.end())
  {
    if(s2.find(*it)!=s2.end())
      s1.erase(it++);
    else ++it;
  } 
}

/*******************************************************************\

Function: uncaught_exceptionst::domaint::set_nonempty_intersection()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T> bool uncaught_exceptionst::domaint::set_nonempty_intersection(
						     const std::set<T> &s1,
						     const std::set<T> &s2)
{
  for(typename std::set<T>::iterator it = s1.begin();
      it != s1.end(); ++it)
  {
    if(s2.find(*it)!=s2.end()) return true;
  }
  return false;
}

/*******************************************************************\

Function: uncaught_exceptionst::domaint::set_equals()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T> bool uncaught_exceptionst::domaint::set_equals(
						  const std::set<T> &s1,
						  const std::set<T> &s2)
{
  return s1==s2;
}

/*******************************************************************\

Function: uncaught_exceptionst::domaint::set_contained()

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

template<class T> bool uncaught_exceptionst::domaint::set_contained(
						     const std::set<T> &s1,
						     const std::set<T> &s2)
{
  for(typename std::set<T>::iterator it = s1.begin();
      it!=s1.end(); ++it)
  {
    if(s2.find(*it)==s2.end()) return false;
  }
  return true;
}


/*******************************************************************\

Function: uncaught_exceptionst::domaint::has_top_exception_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool uncaught_exceptionst::domaint::has_top_exception_type()
{
  return value.size()==1 && value.begin()->second.size()==1 &&
    *value.begin()->second.begin()==top_exception_type;
}

/*******************************************************************\

Function: uncaught_exceptionst::domaint::has_top_location

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool uncaught_exceptionst::domaint::has_top_location()
{
  return value.size()==1 && value.begin()->first.size()==1 &&
    *value.begin()->first.begin()==top_location;
}

/*******************************************************************\

Function: uncaught_exceptionst::is_unknown_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool uncaught_exceptionst::is_unknown_function(
  const irep_idt &function_name) const
{
  goto_functionst::function_mapt::const_iterator f_it = 
    goto_functions.function_map.find(function_name);

  return 
       f_it == goto_functions.function_map.end()
    || (!f_it->second.body_available 
    // TODO: what to do with non-existing standard stuff?
        && function_name != "std::exception::~exception(this)"
        && function_name != "std::exception::what(const$this)");
}

/*******************************************************************\

Function: show_uncaught_exceptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_uncaught_exceptions(
  ui_message_handlert::uit ui,
  const class symbol_tablet &symbol_table,
  const goto_functionst &goto_functions,
  std::ostream &out)
{
  const namespacet ns(symbol_table);

  uncaught_exceptionst uncaught_exceptions(ns, goto_functions);
  
  uncaught_exceptionst::function_exception_mapt exceptions;
  uncaught_exceptions(exceptions);

  switch(ui)
  {
  case ui_message_handlert::XML_UI:
    uncaught_exceptionst::xml_output(out,exceptions);
    break;
      
  case ui_message_handlert::PLAIN:
    uncaught_exceptionst::output(out,exceptions);
    break;

  default:
    assert(false);
  }

#if 0
  out << symbol_table;
#endif
}

/*******************************************************************\

Function: uncaught_exceptionst::output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uncaught_exceptionst::output(std::ostream &out, const domaint &d)
{
  for(uncaught_exceptionst::domaint::valuet::const_iterator
	d_it = d.get().begin(); 
      d_it != d.get().end(); d_it++)
  {
    out << "** Possible types: " << std::endl;
    for(uncaught_exceptionst::domaint::exception_typest::const_iterator
	  e_it = d_it->second.begin(); 
	e_it != d_it->second.end(); e_it++)
      out << "     " << *e_it << std::endl;
    out << "   Possible locations: " << std::endl;
    for(uncaught_exceptionst::domaint::locationst::const_iterator
	  l_it = d_it->first.begin(); 
	l_it != d_it->first.end(); l_it++)
      out << "     " << *l_it << std::endl;
  }
  out << std::endl << std::endl;
}

void uncaught_exceptionst::output(std::ostream &out,
				  const function_exception_mapt &exceptions)
{
  out << "Uncaught exceptions: " << std::endl << std::endl;
  for(function_exception_mapt::const_iterator
	it = exceptions.begin();
      it != exceptions.end(); it++)
  {
    if(it->second.get().size()==0) continue;
    out << "**** Function: " << it->first << std::endl;
    output(out,it->second);
  }
}

/*******************************************************************\

Function: uncaught_exceptionst::xml_output

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void uncaught_exceptionst::xml_output(xmlt &xml, const domaint &d)
{
  for(uncaught_exceptionst::domaint::valuet::const_iterator
	d_it = d.get().begin(); 
      d_it != d.get().end(); d_it++)
  {
    xmlt &ee=xml.new_element("exception");
    xmlt &tt=ee.new_element("types");
    for(uncaught_exceptionst::domaint::exception_typest::const_iterator
	  e_it = d_it->second.begin(); 
	e_it != d_it->second.end(); e_it++)
    {
      tt.new_element("type").data=id2string(*e_it);
    }

    xmlt &ll=xml.new_element("locations");
    for(uncaught_exceptionst::domaint::locationst::const_iterator
	  l_it = d_it->first.begin(); 
	l_it != d_it->first.end(); l_it++)
    {
      xmlt &l=ll.new_element("location");
      l.new_element("line").data=id2string(l_it->get_line());
      l.new_element("file").data=id2string(l_it->get_file());
      l.new_element("function").data=id2string(l_it->get_function());
    }
  }
}

void uncaught_exceptionst::xml_output(std::ostream &out,
				  const function_exception_mapt &exceptions)
{
  xmlt xml("uncaught_exceptions");
  for(function_exception_mapt::const_iterator
	it = exceptions.begin();
      it != exceptions.end(); it++)
  {
    if(it->second.get().size()==0) continue;
    xmlt &f=xml.new_element();
    f.name="function";
    f.set_attribute("id",id2string(it->first));
    xml_output(f,it->second);
  }
  out << xml << std::endl;
}


/*******************************************************************\

Function: uncaught_exceptionst::domaint::cleanup

  Inputs:

 Outputs:

 Purpose:  arrays match with pointers -> rename to ptr

\*******************************************************************/

irep_idt uncaught_exceptionst::domaint::cleanup(irep_idt t)
{
  size_t pos = id2string(t).find("_array");
  if(pos!=std::string::npos) 
    return id2string(t).substr(0,pos)+"_ptr";
  return t;
}

