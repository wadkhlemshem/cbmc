/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <algorithm>
#include <set>
#include <iostream>

#include <util/prefix.h>
#include <util/std_types.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/expr_util.h>
#include <util/cprover_prefix.h>
#include <util/message.h>
#include <util/config.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/i2string.h>
#include <util/prefix.h>

#include <goto-programs/goto_functions.h>

#include "java_entry_point.h"

//#include "zero_initializer.h"

#define INITIALIZE CPROVER_PREFIX "initialize"

/*******************************************************************\

Function: create_initialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
void create_initialize(symbol_tablet &symbol_table)
{
  symbolt initialize;
  initialize.name=INITIALIZE;
  initialize.base_name=INITIALIZE;
  initialize.mode=ID_java;

  code_typet type;
  type.return_type()=empty_typet();
  initialize.type=type;
  
  code_blockt init_code;
  
  namespacet ns(symbol_table);
  
  symbol_exprt rounding_mode=
    ns.lookup(CPROVER_PREFIX "rounding_mode").symbol_expr();

  init_code.add(code_assignt(rounding_mode, gen_zero(rounding_mode.type())));
  
  initialize.value=init_code;
  
  if(symbol_table.add(initialize))
    throw "failed to add "+std::string(INITIALIZE);
}
}

/*******************************************************************\

Function: gen_nondet_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
  symbolt &new_tmp_symbol(symbol_tablet &symbol_table, const std::string& prefix = "tmp_struct_init")
{
  static int temporary_counter=0;

  auxiliary_symbolt new_symbol;
  symbolt *symbol_ptr;

  do
  {
    new_symbol.name=prefix+'$'+i2string(++temporary_counter);
    new_symbol.base_name=new_symbol.name;
    new_symbol.mode=ID_java;
  } while(symbol_table.move(new_symbol, symbol_ptr));

  return *symbol_ptr;
}
}

/*******************************************************************\

Function: gen_nondet_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  std::set<irep_idt> &recursion_set,
  bool is_sub,
  irep_idt class_identifier,
  bool skip_classid = false)
{
  const namespacet ns(symbol_table);
  const typet &type=ns.follow(expr.type());
  
  if(type.id()==ID_pointer)
  {
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &subtype=ns.follow(pointer_type.subtype());

    if(subtype.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(subtype);
      const irep_idt struct_tag=struct_type.get_tag();

      if(recursion_set.find(struct_tag)!=recursion_set.end())
      {
        // make null
        null_pointer_exprt null_pointer_expr(pointer_type);
        code_assignt code(expr, null_pointer_expr);
        init_code.copy_to_operands(code);

        return;
      }
    }

    symbolt &aux_symbol=new_tmp_symbol(symbol_table);
    aux_symbol.type=subtype;
    aux_symbol.is_static_lifetime=true;

    exprt object=aux_symbol.symbol_expr();
    gen_nondet_init(object, init_code, symbol_table, recursion_set, false, "");

    address_of_exprt aoe(object);

    code_assignt code(expr, aoe);
    init_code.copy_to_operands(code);

    #if 0
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &subtype=ns.follow(pointer_type.subtype());

    if(subtype.id()==ID_struct)
    {
      const struct_typet &struct_type=to_struct_type(subtype);
      const irep_idt struct_tag=struct_type.get_tag();

      if(recursion_set.find(struct_tag)!=recursion_set.end())
      {
        // make null
        null_pointer_exprt null_pointer_expr(pointer_type);
        code_assignt code(expr, null_pointer_expr);
        init_code.copy_to_operands(code);

        return;
      }
    }

    // build size expression
    exprt object_size=size_of_expr(subtype, ns);

    if(subtype.id()!=ID_empty && !object_size.is_nil())
    {
      // malloc expression
      side_effect_exprt malloc_expr(ID_malloc);
      malloc_expr.copy_to_operands(object_size);
      malloc_expr.type()=pointer_type;

      code_assignt code(expr, malloc_expr);
      init_code.copy_to_operands(code);

      // dereference expression
      dereference_exprt deref_expr(expr, subtype);

      gen_nondet_init(deref_expr, init_code, ns, recursion_set, false, "");
    }
    else
    {
      // make null
      null_pointer_exprt null_pointer_expr(pointer_type);
      code_assignt code(expr, null_pointer_expr);
      init_code.copy_to_operands(code);
    }
    #endif
  }
  else if(type.id()==ID_struct)
  {
    typedef struct_typet::componentst componentst;

    const struct_typet &struct_type=to_struct_type(type);
    const irep_idt struct_tag=struct_type.get_tag();

    const componentst &components=struct_type.components();
    
    if(!is_sub)
      class_identifier=struct_tag;

    recursion_set.insert(struct_tag);
    assert(!recursion_set.empty());
    
    for(const auto &component : components)
    {
      const typet &component_type=component.type();
      irep_idt name=component.get_name();

      member_exprt me(expr, name, component_type);

      if(name=="@class_identifier")
      {

	if(skip_classid)
	  continue;
	
        constant_exprt ci(class_identifier, string_typet());

        code_assignt code(me, ci);
        init_code.copy_to_operands(code);
      }
      else
      {
        assert(!name.empty());

        bool _is_sub=name[0]=='@';
#if 0
        irep_idt _class_identifier=
          _is_sub?(class_identifier.empty()?struct_tag:class_identifier):"";
#endif

        gen_nondet_init(me, init_code, symbol_table, recursion_set, _is_sub,
          class_identifier);
      }
    }

    recursion_set.erase(struct_tag);
  }
  else
  {
    side_effect_expr_nondett se=side_effect_expr_nondett(type);

    code_assignt code(expr, se);
    init_code.copy_to_operands(code);
  }
}
}

/*******************************************************************\

Function: gen_nondet_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {
void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  bool skip_classid = false)
{
  std::set<irep_idt> recursion_set;
  gen_nondet_init(expr, init_code, symbol_table, recursion_set, false, "", skip_classid);
}
}

/*******************************************************************\

Function: gen_argument

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {

exprt get_nondet_bool(const typet& type) {
  // We force this to 0 and 1 and won't consider
  // other values.
  return typecast_exprt(side_effect_expr_nondett(bool_typet()), type);
}

exprt gen_argument(
  const typet &type,
  code_blockt &init_code,
  bool is_this,
  bool allow_null,
  symbol_tablet &symbol_table)
{
  if(type.id()==ID_pointer)
  {
    symbolt &aux_symbol=new_tmp_symbol(symbol_table);
    aux_symbol.type=type.subtype();
    aux_symbol.is_static_lifetime=true;

    exprt object=aux_symbol.symbol_expr();
    
    gen_nondet_init(object, init_code, symbol_table);

    // todo: need to pass null, possibly
    return address_of_exprt(object);
  }
  else if(type.id()==ID_c_bool)
    return get_nondet_bool(type);
  else
    return side_effect_expr_nondett(type);
}
}

/*******************************************************************\

Function: java_static_lifetime_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_static_lifetime_init(
  symbol_tablet &symbol_table,
  const source_locationt &source_location,
  message_handlert &message_handler)
{
  symbolt &initialize_symbol=symbol_table.lookup(INITIALIZE);
  code_blockt &code_block=to_code_block(to_code(initialize_symbol.value));
  
  // we need to zero out all static variables
  
  for(symbol_tablet::symbolst::const_iterator
      it=symbol_table.symbols.begin();
      it!=symbol_table.symbols.end();
      it++)
  {
    if(it->second.type.id()!=ID_code &&
       it->second.is_lvalue &&
       it->second.is_state_var &&
       it->second.is_static_lifetime &&
       it->second.value.is_not_nil() &&
       it->second.mode==ID_java)
    {
      code_assignt assignment(it->second.symbol_expr(), it->second.value);
      code_block.add(assignment);
    }
  }
  
  // we now need to run all the <clinit> methods

  for(symbol_tablet::symbolst::const_iterator
      it=symbol_table.symbols.begin();
      it!=symbol_table.symbols.end();
      it++)
  {
    if(it->second.base_name=="<clinit>" &&
       it->second.type.id()==ID_code &&
       it->second.mode==ID_java)
    {
      code_function_callt function_call;
      function_call.lhs()=nil_exprt();
      function_call.function()=it->second.symbol_expr();
      code_block.add(function_call);
    }
  }
  
  return false;
}

/*******************************************************************\

Function: java_entry_point

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool java_entry_point(
  symbol_tablet &symbol_table,
  const irep_idt &main_class,
  message_handlert &message_handler)
{
  // check if the entry point is already there
  if(symbol_table.symbols.find(goto_functionst::entry_point())!=
     symbol_table.symbols.end())
    return false; // silently ignore

  messaget message(message_handler);

  symbolt symbol; // main function symbol

  // find main symbol
  if(config.main!="")
  {
    // Add java:: prefix
    std::string main_identifier="java::"+config.main;
    
    symbol_tablet::symbolst::const_iterator s_it;
    
    // Does it have a type signature? (':' suffix)
    if(config.main.rfind(':')==std::string::npos)
    {
      std::string prefix=main_identifier+':';
      std::set<irep_idt> matches;
      
      for(const auto & s : symbol_table.symbols)
        if(has_prefix(id2string(s.first), prefix) &&
           s.second.type.id()==ID_code)
          matches.insert(s.first);

      if(matches.empty())
      {
        message.error() << "main symbol `" << config.main
                        << "' not found" << messaget::eom;
        return true;
      }
      else if(matches.size()==1)
      {
        s_it=symbol_table.symbols.find(*matches.begin());
        assert(s_it!=symbol_table.symbols.end());
      }
      else
      {
        message.error() << "main symbol `" << config.main
                        << "' is ambiguous:\n";

        for(const auto & s : matches)
          message.error() << "  " << s << '\n';
        
        message.error() << messaget::eom;

        return true;
      }
    }
    else
    {
      // just look it up
      s_it=symbol_table.symbols.find(main_identifier);

      if(s_it==symbol_table.symbols.end())
      {
        message.error() << "main symbol `" << config.main
                        << "' not found" << messaget::eom;
        return true;
      }
    }

    // function symbol
    symbol=s_it->second;

    if(symbol.type.id()!=ID_code)
    {
      message.error() << "main symbol `" << config.main
                      << "' not a function" << messaget::eom;
      return true;
    }
    
    // check if it has a body
    if(symbol.value.is_nil())
    {
      message.error() << "main method `" << main_class
                      << "' has no body" << messaget::eom;
      return true;
    }
  }
  else
  {
    // no function given, we look for the main class
    assert(config.main=="");

    // are we given a main class?
    if(main_class.empty())
      return false; // silently ignore

    std::string entry_method=
      id2string(main_class)+".main";

    std::string prefix="java::"+entry_method+":";

    // look it up
    std::set<irep_idt> matches;

    for(symbol_tablet::symbolst::const_iterator
        s_it=symbol_table.symbols.begin();
        s_it!=symbol_table.symbols.end();
        s_it++)
    {
      if(s_it->second.type.id()==ID_code &&
         has_prefix(id2string(s_it->first), prefix))
        matches.insert(s_it->first);
    }

    if(matches.empty())
    {
      // Not found, silently ignore
      return false;
    }

    if(matches.size()>=2)
    {
      message.error() << "main method in `" << main_class
                      << "' is ambiguous" << messaget::eom;
      return true; // give up with error, no main
    }

    // function symbol
    symbol=symbol_table.symbols.find(*matches.begin())->second;
  
    // check if it has a body
    if(symbol.value.is_nil())
    {
      message.error() << "main method `" << main_class
                      << "' has no body" << messaget::eom;
      return true; // give up with error
    }
  }

  assert(!symbol.value.is_nil());
  assert(symbol.type.id()==ID_code);

  const code_typet &code_type=to_code_type(symbol.type);
    
  create_initialize(symbol_table);

  if(java_static_lifetime_init(symbol_table, symbol.location, message_handler))
    return true;

  code_blockt init_code;

  // build call to initialization function
  {
    symbol_tablet::symbolst::iterator init_it=
      symbol_table.symbols.find(INITIALIZE);

    if(init_it==symbol_table.symbols.end())
    {
      message.error() << "failed to find " INITIALIZE " symbol"
                      << messaget::eom;
      return true; // give up with error
    }

    code_function_callt call_init;
    call_init.lhs().make_nil();
    call_init.add_source_location()=symbol.location;
    call_init.function()=init_it->second.symbol_expr();

    init_code.move_to_operands(call_init);
  }

  // build call to the main method

  code_function_callt call_main;
  call_main.add_source_location()=symbol.location;
  call_main.function()=symbol.symbol_expr();

  const code_typet::parameterst &parameters=
    code_type.parameters();

  exprt::operandst main_arguments;
  main_arguments.resize(parameters.size());
  
  for(std::size_t param_number=0;
      param_number<parameters.size();
      param_number++)
  {
    bool is_this=param_number==0 &&
                 parameters[param_number].get_this();
    bool allow_null=config.main!="";
    
    main_arguments[param_number]=
      gen_argument(parameters[param_number].type(), 
                   init_code, is_this, allow_null, symbol_table);
  }

  call_main.arguments()=main_arguments;

  init_code.move_to_operands(call_main);

  // add "main"
  symbolt new_symbol;

  code_typet main_type;
  main_type.return_type()=empty_typet();

  new_symbol.name=goto_functionst::entry_point();
  new_symbol.type.swap(main_type);
  new_symbol.value.swap(init_code);
  new_symbol.mode=ID_java;

  if(symbol_table.move(new_symbol))
  {
    message.error() << "failed to move main symbol" << messaget::eom;
    return true;
  }

  return false;
}

namespace { // Anon namespace for insert-nondet support functions

exprt clean_deref(const exprt ptr) {

  return ptr.id() == ID_address_of ? ptr.op0() : dereference_exprt(ptr, ptr.type().subtype());
  
}

bool find_superclass_with_type(exprt& ptr, const typet& target_type, const namespacet& ns) {

  while(true) {
  
    const typet ptr_base = ns.follow(ptr.type().subtype());
  
    if(ptr_base.id() != ID_struct)
      return false;

    const struct_typet& base_struct = to_struct_type(ptr_base);

    if(base_struct.components().size() == 0)
      return false;

    const typet& first_field_type = ns.follow(base_struct.components()[0].type());
    ptr = clean_deref(ptr);
    ptr = member_exprt(ptr, base_struct.components()[0].get_name(), first_field_type);
    ptr = address_of_exprt(ptr);

    if(first_field_type == target_type)
      return true;

  }

}
  
exprt make_clean_pointer_cast(const exprt ptr, const typet& target_type, const namespacet& ns) {

  assert(target_type.id() == ID_pointer && "Non-pointer target in make_clean_pointer_cast?");
  
  if(ptr.type() == target_type)
    return ptr;

  const typet& target_base = ns.follow(target_type.subtype());

  exprt bare_ptr = ptr;
  while(bare_ptr.id() == ID_typecast) {
    assert(bare_ptr.type().id() == ID_pointer && "Non-pointer in make_clean_pointer_cast?");
    if(bare_ptr.type().subtype() == empty_typet())
      bare_ptr = bare_ptr.op0();
  }

  assert(bare_ptr.type().id() == ID_pointer && "Non-pointer in make_clean_pointer_cast?");

  if(bare_ptr.type() == target_type)
    return bare_ptr;

  exprt superclass_ptr = bare_ptr;
  if(find_superclass_with_type(superclass_ptr, target_base, ns))
    return superclass_ptr;
  
  return typecast_exprt(bare_ptr, target_type);

}

void insert_nondet_opaque_fields_at(const typet& expected_type, const exprt &ptr, symbol_tablet& symbol_table, code_blockt* parent_block, unsigned insert_after_index, bool is_constructor) {

  // At this point we know 'ptr' points to an opaque-typed object. We should nondet-initialise it
  // and insert the instructions *after* the offending call at (*parent_block)[insert_after_index].

  assert(expected_type.id() == ID_pointer && "Nondet initialiser should have pointer type");
  assert(parent_block && "Must have an existing block to insert nondet-init code");

  bool assume_non_null = getenv("CBMC_OPAQUE_RETURNS_NON_NULL") != 0;  

  namespacet ns(symbol_table);

  const auto& expected_base = ns.follow(expected_type.subtype());
  if(expected_base.id() != ID_struct)
    return;
  
  const exprt cast_ptr = make_clean_pointer_cast(ptr, expected_type, ns);
  code_labelt set_null_label;
  code_labelt init_done_label;

  code_blockt new_instructions;

  if(!is_constructor) {

    // Per default CBMC would suppose this to be any conceivable pointer.
    // For now, insist that it is either fresh or null. In future we will
    // want to consider the possiblity that it aliases other objects.
    
    static unsigned long synthetic_constructor_count = 0;

    if(!assume_non_null) {

      auto returns_null_sym = new_tmp_symbol(symbol_table, "opaque_returns_null");
      returns_null_sym.type = c_bool_typet(1);
      auto returns_null = returns_null_sym.symbol_expr();
      auto assign_returns_null = code_assignt(returns_null, get_nondet_bool(returns_null_sym.type));
      new_instructions.move_to_operands(assign_returns_null);

      auto set_null_inst = code_assignt(cast_ptr, null_pointer_exprt(to_pointer_type(cast_ptr.type())));
      set_null_inst.set("overwrites_return_value", true);

      std::ostringstream fresh_label_oss;
      fresh_label_oss << "post_synthetic_malloc_" << (++synthetic_constructor_count);
      std::string fresh_label = fresh_label_oss.str();
      set_null_label = code_labelt(fresh_label, set_null_inst);

      init_done_label = code_labelt(fresh_label + "_init_done", code_skipt());

      code_ifthenelset null_check;
      null_check.cond() = notequal_exprt(returns_null, constant_exprt("0", returns_null_sym.type));
      null_check.then_case() = code_gotot(fresh_label);
      new_instructions.move_to_operands(null_check);

    }

    // Note this allocates memory but doesn't call any constructor.
    side_effect_exprt malloc_expr(ID_malloc);
    malloc_expr.copy_to_operands(size_of_expr(expected_base, ns));
    malloc_expr.type() = expected_type;
    auto alloc_inst = code_assignt(cast_ptr, malloc_expr);
    alloc_inst.set("overwrites_return_value", true);
    new_instructions.move_to_operands(alloc_inst);

  }

  exprt derefd = clean_deref(cast_ptr);
  
  gen_nondet_init(derefd, new_instructions, symbol_table, is_constructor);

  if((!is_constructor) && !assume_non_null) {
    new_instructions.copy_to_operands(code_gotot(init_done_label.get_label()));    
    new_instructions.move_to_operands(set_null_label);
    new_instructions.move_to_operands(init_done_label);
  }
  
  if(new_instructions.operands().size() != 0) {

    auto institer = parent_block->operands().begin();
    std::advance(institer, insert_after_index + 1);
    parent_block->operands().insert(institer, new_instructions.operands().begin(), new_instructions.operands().end());
    
  }

}
bool is_opaque_type(const typet& t, const symbol_tablet& symtab) {

  if(t.id() == ID_pointer)
    return is_opaque_type(t.subtype(), symtab);
  
  namespacet ns(symtab);
  const typet& resolved = ns.follow(t);

  // No point trying to initalise opaque types without fields.
  return resolved.get_bool(ID_incomplete_class) && to_class_type(resolved).components().size() != 0;

}
  
void insert_nondet_opaque_fields(codet &code, symbol_tablet& symbol_table, code_blockt* parent, unsigned parent_index) {

  const irep_idt &statement=code.get_statement();

  // TOCHECK: is this enough to iterate over all call instructions?
  
  if(statement==ID_block) {

    // Use indices not iterators as instructions are added as we progress.
    for(unsigned i = 0; i < code.operands().size(); ++i)
      insert_nondet_opaque_fields(to_code(code.operands()[i]), symbol_table, &to_code_block(code), i);
    
  }
  else if(statement == ID_ifthenelse) {

    code_ifthenelset &code_ifthenelse=to_code_ifthenelse(code);
    insert_nondet_opaque_fields(code_ifthenelse.then_case(), symbol_table, parent, parent_index);
    if(code_ifthenelse.else_case().is_not_nil())
      insert_nondet_opaque_fields(code_ifthenelse.else_case(), symbol_table, parent, parent_index);
    
  }
  else if(statement == ID_function_call) {

    code_function_callt &code_function_call=to_code_function_call(code);
    const exprt& callee = code_function_call.function();
    const code_typet& callee_type = to_code_type(callee.type());
    namespacet ns(symbol_table);
    
    bool is_opaque_call = false;

    if(callee.id() == ID_symbol) {

      // Static call. Constructors should blat their this-arg with nondets;
      // other static calls should blat any opaque objects they return.
      
      const symbolt& target = ns.lookup(callee);

      if(!target.value.is_nil())
	return; // Known target.
      
      const std::string& id = id2string(to_symbol_expr(callee).get_identifier());
      bool is_constructor = id.find("<init>") != std::string::npos
	|| id.find("<clinit>") != std::string::npos;
      
      if(is_constructor)
	insert_nondet_opaque_fields_at(callee_type.parameters()[0].type(),
				       code_function_call.arguments()[0],
				       symbol_table, parent, parent_index, true);
      else if(is_opaque_type(callee_type.return_type(), symbol_table))
	insert_nondet_opaque_fields_at(callee_type.return_type(),
				       code_function_call.lhs(),
				       symbol_table, parent, parent_index, false);

    }
    else {

      // Dynamic dispatch. Assume opaque if the pointer type is opaque
      // (but in truth it could be worse, as external code could supply
      // an override we don't know about)

      assert(callee_type.has_this() && "Dynamic dispatch but not instance method?");
      if(is_opaque_type(code_function_call.arguments()[0].type(), symbol_table)
	 && is_opaque_type(callee_type.return_type(), symbol_table)) {
	
	insert_nondet_opaque_fields_at(callee_type.return_type(),
				       code_function_call.lhs(),
				       symbol_table, parent, parent_index, false);
	
      }

	
    }
    
  }

}
  
void insert_nondet_opaque_fields(symbolt &sym, symbol_tablet &symbol_table) {

  if(sym.is_type)
    return;
  if(sym.value.id() != ID_code)
    return;

  insert_nondet_opaque_fields(to_code(sym.value), symbol_table, 0, 0);

}

} // End anon namespace for insert-nondet support functions

void java_insert_nondet_opaque_objects(symbol_tablet &symbol_table) {

  std::vector<irep_idt> identifiers;
  identifiers.reserve(symbol_table.symbols.size());
  forall_symbols(s_it, symbol_table.symbols)
    identifiers.push_back(s_it->first);

  for(auto& id : identifiers)
    insert_nondet_opaque_fields(symbol_table.symbols[id], symbol_table);

}
