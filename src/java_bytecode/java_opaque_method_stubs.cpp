
#include <util/std_expr.h>
#include <util/std_code.h>
#include <util/pointer_offset_size.h>
#include <util/i2string.h>
#include <util/namespace.h>
#include <util/prefix.h>

#include "java_object_factory.h"

namespace
{ // Anon namespace for insert-nondet support functions

exprt clean_deref(const exprt ptr)
{

  return ptr.id()==ID_address_of
             ? ptr.op0()
             : dereference_exprt(ptr,ptr.type().subtype());
}

bool find_superclass_with_type(exprt &ptr,const typet &target_type,
                               const namespacet &ns)
{

  while(true)
  {

    const typet ptr_base=ns.follow(ptr.type().subtype());

    if(ptr_base.id()!=ID_struct)
      return false;

    const struct_typet &base_struct=to_struct_type(ptr_base);

    if(base_struct.components().size()==0)
      return false;

    const typet &first_field_type=
        ns.follow(base_struct.components()[0].type());
    ptr=clean_deref(ptr);
    ptr=member_exprt(ptr,base_struct.components()[0].get_name(),
                      first_field_type);
    ptr=address_of_exprt(ptr);

    if(first_field_type==target_type)
      return true;
  }
}

exprt make_clean_pointer_cast(const exprt ptr,const typet &target_type,
                              const namespacet &ns)
{

  assert(target_type.id()==ID_pointer &&
         "Non-pointer target in make_clean_pointer_cast?");

  if(ptr.type()==target_type)
    return ptr;

  const typet &target_base=ns.follow(target_type.subtype());

  exprt bare_ptr=ptr;
  while(bare_ptr.id()==ID_typecast)
  {
    assert(bare_ptr.type().id()==ID_pointer &&
           "Non-pointer in make_clean_pointer_cast?");
    if(bare_ptr.type().subtype()==empty_typet())
      bare_ptr=bare_ptr.op0();
  }

  assert(bare_ptr.type().id()==ID_pointer &&
         "Non-pointer in make_clean_pointer_cast?");

  if(bare_ptr.type()==target_type)
    return bare_ptr;

  exprt superclass_ptr=bare_ptr;
  if(find_superclass_with_type(superclass_ptr,target_base,ns))
    return superclass_ptr;

  return typecast_exprt(bare_ptr,target_type);
}

void insert_nondet_opaque_fields_at(const typet &expected_type,
                                    const exprt &ptr,
                                    symbol_tablet &symbol_table,
                                    code_blockt *parent_block,
                                    unsigned insert_before_index,
                                    bool is_constructor,bool assume_non_null)
{

  // At this point we know 'ptr' points to an opaque-typed object. We should
  // nondet-initialise it
  // and insert the instructions *after* the offending call at
  // (*parent_block)[insert_before_index].

  assert(expected_type.id()==ID_pointer &&
         "Nondet initialiser should have pointer type");
  assert(parent_block &&
         "Must have an existing block to insert nondet-init code");

  namespacet ns(symbol_table);

  const auto &expected_base=ns.follow(expected_type.subtype());
  if(expected_base.id()!=ID_struct)
    return;

  const exprt cast_ptr=make_clean_pointer_cast(ptr,expected_type,ns);
  code_blockt new_instructions;

  exprt to_init=cast_ptr;
  // If it's a constructor the thing we're constructing has already
  // been allocated by this point.
  if(is_constructor)
    to_init=dereference_exprt(to_init,expected_base);

  gen_nondet_init(to_init,new_instructions,symbol_table,false,true);

  if(new_instructions.operands().size()!=0)
  {

    auto institer=parent_block->operands().begin();
    std::advance(institer,insert_before_index);
    parent_block->operands().insert(institer,
                                    new_instructions.operands().begin(),
                                    new_instructions.operands().end());
  }
}

void assign_parameter_names(code_typet &ftype,const irep_idt &name_prefix,
                            symbol_tablet &symbol_table)
{

  code_typet::parameterst &parameters=ftype.parameters();

  // Mostly borrowed from java_bytecode_convert.cpp; maybe factor this out.
  // assign names to parameters
  for(std::size_t i=0; i<parameters.size(); ++i)
  {
    irep_idt base_name,identifier;

    if(i==0 && parameters[i].get_this())
      base_name="this";
    else
      base_name="stub_ignored_arg" + i2string(i);

    identifier=id2string(name_prefix) + "::" + id2string(base_name);
    parameters[i].set_base_name(base_name);
    parameters[i].set_identifier(identifier);

    // add to symbol table
    parameter_symbolt parameter_symbol;
    parameter_symbol.base_name=base_name;
    parameter_symbol.mode=ID_java;
    parameter_symbol.name=identifier;
    parameter_symbol.type=parameters[i].type();
    symbol_table.add(parameter_symbol);
  }
}

void insert_nondet_opaque_fields(symbolt &sym,symbol_tablet &symbol_table,
                                 code_blockt *parent,unsigned parent_index,
                                 bool assume_non_null)
{

  code_blockt new_instructions;
  code_typet &required_type=to_code_type(sym.type);
  namespacet ns(symbol_table);

  bool is_constructor=sym.type.get_bool(ID_constructor);

  if(!is_constructor)
  {
    const auto &needed=required_type.return_type();
    if(needed.id()!=ID_pointer)
    {
      // Returning a primitive -- no point generating a stub.
      return;
    }
  }

  assign_parameter_names(required_type,sym.name,symbol_table);

  if(is_constructor)
  {
    const auto &thisarg=required_type.parameters()[0];
    const auto &thistype=thisarg.type();
    auto &init_symbol=new_tmp_symbol(symbol_table,"to_construct");
    init_symbol.type=thistype;
    const auto init_symexpr=init_symbol.symbol_expr();
    auto getarg=
        code_assignt(init_symexpr,symbol_exprt(thisarg.get_identifier()));
    new_instructions.copy_to_operands(getarg);
    insert_nondet_opaque_fields_at(thistype,init_symexpr,symbol_table,
                                   &new_instructions,1,true,assume_non_null);
    sym.type.set("opaque_method_capture_symbol",init_symbol.name);
  }
  else
  {
    auto &toreturn_symbol=new_tmp_symbol(symbol_table,"to_return");
    toreturn_symbol.type=required_type.return_type();
    auto toreturn_symexpr=toreturn_symbol.symbol_expr();
    insert_nondet_opaque_fields_at(
        required_type.return_type(),toreturn_symexpr,symbol_table,
        &new_instructions,0,false,assume_non_null);
    new_instructions.copy_to_operands(code_returnt(toreturn_symexpr));
    sym.type.set("opaque_method_capture_symbol",toreturn_symbol.name);
  }

  sym.value=new_instructions;
}

void insert_nondet_opaque_fields(symbolt &sym,symbol_tablet &symbol_table,
                                 bool assume_non_null)
{

  if(sym.is_type)
    return;
  if(sym.value.id()!=ID_nil)
    return;
  if(sym.type.id()!=ID_code)
    return;

  insert_nondet_opaque_fields(sym,symbol_table,0,0,assume_non_null);
}

} // End anon namespace for insert-nondet support functions

void java_generate_opaque_method_stubs(symbol_tablet &symbol_table,
                                       bool assume_non_null)
{

  std::vector<irep_idt>identifiers;
  identifiers.reserve(symbol_table.symbols.size());
  forall_symbols(s_it,symbol_table.symbols) identifiers.push_back(s_it->first);

  for(auto &id : identifiers)
    insert_nondet_opaque_fields(symbol_table.symbols[id],symbol_table,
                                assume_non_null);
}
