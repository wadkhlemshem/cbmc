/*******************************************************************\

Module: Value Set

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#include <util/prefix.h>
#include <util/std_code.h>

#include "value_set_domain.h"


/*******************************************************************\

Function: value_set_domaint::merge_shared

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_domaint::merge_shared(
  const namespacet &ns,
  const value_set_domaint &other,
  locationt to)
{
    // TODO: dirty vars
#if 0
  reaching_definitions_analysist *rd=
    dynamic_cast<reaching_definitions_analysist*>(&ai);
  assert(rd!=0);
#endif


  hash_set_cont<irep_idt, irep_id_hash> selected_vars;

  for(value_sett::valuest::const_iterator ito=other.value_set.values.begin();
      ito!=other.value_set.values.end();
      ++ito)
  {
    const irep_idt &identifier=ito->first;

    #ifdef DEBUG
      std::cout << "Symbol " << identifier << std::endl;
    #endif

    if(has_prefix(id2string(identifier), "value_set::"))
      continue;

    if(!is_shared(identifier, ns) /*&&
       !rd.get_is_dirty()(identifier)*/)
      continue;
    
    selected_vars.insert(identifier);

    #ifdef DEBUG
      std::cout << "   SHARED " << std::endl;
    #endif

  }
    
  return value_set.make_union(other.value_set.values, selected_vars);
}


/*******************************************************************\

Function: value_set_domaint::transform

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void value_set_domaint::transform(
  const namespacet &ns,
  locationt from_l,
  locationt to_l)
{
  switch(from_l->type)
  {
  case GOTO:
    // ignore for now
    break;

  case END_FUNCTION:    
    value_set.do_end_function(static_analysis_baset::get_return_lhs(to_l), ns);
    break;
  
  case RETURN:
  case OTHER:
  case ASSIGN:
  case DECL:
    value_set.apply_code(from_l->code, ns);
    break;
    
  case ASSUME:
    value_set.guard(from_l->guard, ns);
    break;

  case FUNCTION_CALL:
    {
      const code_function_callt &code=
        to_code_function_call(from_l->code);

      value_set.do_function_call(to_l->function, code.arguments(), ns);
    }
    break;
  
  case DEAD:
    {
      const code_deadt &code=
         to_code_dead(from_l->code);
      value_set.values.erase(code.get_identifier());
    }
    break;
  
  default:;
    // do nothing
  }
}

/*******************************************************************\

Function: value_set_domaint::is_shared

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool value_set_domaint::is_shared(
  const irep_idt &identifier,
  const namespacet &ns)
{
  std::string id=id2string(identifier);

  // get identifier of root object: struct
  std::size_t pos_dot=id.find('.');
  id=id.substr(0,pos_dot);

  std::size_t pos_bracket=id.find('[');
  id=id.substr(0,pos_bracket);

  const symbolt &symbol=ns.lookup(id);

  bool result=symbol.is_shared();

  return result;
}

