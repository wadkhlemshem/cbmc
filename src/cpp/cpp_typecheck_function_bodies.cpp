/*******************************************************************\

Module: C++ Language Type Checking

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

//#define DEBUG

#ifdef DEBUG
#include <iostream>
#endif

#include <util/i2string.h>

#include "cpp_typecheck.h"

/*******************************************************************\

Function: cpp_typecheckt::typecheck_function_bodies

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::typecheck_function_bodies()
{
  instantiation_stackt old_instantiation_stack;
  old_instantiation_stack.swap(instantiation_stack);

  while(!function_bodies.empty())
  {
    //Dangerous not to take a copy here. We'll have to make sure that
    //  convert is never called with the same symbol twice.
#if 1
    function_bodyt &function_body = *function_bodies.begin();
#else
    function_bodyt &function_body = function_bodies.begin()->second;
#endif
    symbolt &function_symbol = *function_body.function_symbol;
    
    template_map.swap(function_body.template_map);
    instantiation_stack.swap(function_body.instantiation_stack);

#if 0
    std::cout << "MAP for " << function_symbol.name << ":" << std::endl;
    template_map.print(std::cout);
#endif 
    function_bodies.erase(function_bodies.begin());

    if(function_symbol.name==ID_main)
      add_argc_argv(function_symbol);

    exprt &body=function_symbol.value;
    if(body.id()=="cpp_not_typechecked")
      continue;

#ifdef DEBUG
  std::cout << "convert_function_body: " << function_symbol.name << std::endl;
  std::cout << "  is_not_nil: " << body.is_not_nil() << std::endl;
  std::cout << "  !is_zero: " << (!body.is_zero()) << std::endl;
#endif
    if(body.is_not_nil() &&
       !body.is_zero())
    {
      convert_function(function_symbol);
    }
  }

  old_instantiation_stack.swap(instantiation_stack);
}

/*******************************************************************\

Function: cpp_typecheckt::add_function_body

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_typecheckt::add_function_body(symbolt *_function_symbol)
{
#ifdef DEBUG
  std::cout << "add_function_body: " << _function_symbol->name << std::endl;
#endif
  //TODO: cleanup
#if 1
  // We have to prevent the same function to be added multiple times
  //   otherwise we get duplicated symbol prefixes
  if(functions_seen.find(_function_symbol->name) != functions_seen.end())
  {
#ifdef DEBUG
    std::cout << "  already exists" << std::endl;
#endif 
    return;
  }
  function_bodies.push_back(function_bodyt(
			      _function_symbol, template_map, instantiation_stack));

  
  // Converting a function body might add function bodies for functions
  // that we have already analyzed. Hence, we have to keep track.
  functions_seen.insert(_function_symbol->name);
#else
  if(function_bodies.find(_function_symbol->name) != function_bodies.end())
  {
#ifdef DEBUG
    std::cout << "  already exists" << std::endl;
    if(function_bodies[_function_symbol->name].function_symbol->value != 
       _function_symbol->value)
    {
      std::cout << "  OLD: " << function_bodies[_function_symbol->name].function_symbol->value.pretty() << std::endl;
      std::cout << "  NEW: " << _function_symbol->value.pretty() << std::endl;
    }
#endif 
  }
  else
  {
    function_bodyt &fb = function_bodies[_function_symbol->name];
    fb.function_symbol = _function_symbol;
    fb.template_map = template_map;
    fb.instantiation_stack = instantiation_stack;
  }
#endif
}
