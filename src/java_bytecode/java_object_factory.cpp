/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <set>

#include <util/std_types.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/i2string.h>
#include <util/namespace.h>
#include <util/pointer_offset_size.h>
#include <util/prefix.h>

#include "java_object_factory.h"

/*******************************************************************\

Function: gen_nondet_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

namespace {

// Returns false if we can't figure out the size of allocate_type.
// allocate_type may differ from target_expr, e.g. for target_expr having
// type int* and allocate_type being an int[10].
bool allocate_object(
  const exprt& target_expr,
  const typet& allocate_type,
  code_blockt& init_code,
  symbol_tablet& symbol_table,
  bool create_dynamic_objects)
{
  if(!create_dynamic_objects)
  {
    symbolt &aux_symbol=new_tmp_symbol(symbol_table);
    aux_symbol.type=allocate_type;
    aux_symbol.is_static_lifetime=true;
      
    exprt object=aux_symbol.symbol_expr();
    exprt aoe=address_of_exprt(object);
    if(aoe.type()!=target_expr.type())
      aoe=typecast_exprt(aoe, target_expr.type());
    code_assignt code(target_expr,aoe);
    init_code.copy_to_operands(code);
    return true;
  }
  else
  {
    // build size expression
    exprt object_size=size_of_expr(allocate_type, namespacet(symbol_table));

    if(allocate_type.id()!=ID_empty && !object_size.is_nil())
    {
      // malloc expression
      exprt malloc_expr = side_effect_exprt(ID_malloc);
      malloc_expr.copy_to_operands(object_size);
      typet result_type=pointer_typet(allocate_type);
      malloc_expr.type()=result_type;
      if(malloc_expr.type()!=target_expr.type())
        malloc_expr=typecast_exprt(malloc_expr,target_expr.type());
      code_assignt code(target_expr, malloc_expr);
      init_code.copy_to_operands(code);
      return true;
    }
    else
    {
      // make null
      null_pointer_exprt null_pointer_expr(to_pointer_type(target_expr.type()));
      code_assignt code(target_expr, null_pointer_expr);
      init_code.copy_to_operands(code);
      return false;
    }
  }
}

void gen_nondet_array_init(const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  std::set<irep_idt> &recursion_set,
  bool create_dynamic_objects);

// Override type says to ignore the LHS' real type, and init it with the given
// type regardless. Used at the moment for reference arrays, which are implemented
// as void* arrays but should be init'd as their true type with appropriate casts.
void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  std::set<irep_idt> &recursion_set,
  bool is_sub,
  irep_idt class_identifier,
  bool skip_classid,
  bool create_dynamic_objects,
  const typet *override_type = 0)
{
  namespacet ns(symbol_table);
  const typet &type=
    override_type ? ns.follow(*override_type) : ns.follow(expr.type());
  
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

    if(allocate_object(expr,subtype,init_code,symbol_table,create_dynamic_objects))
    {
      exprt init_expr=expr;
      if(override_type)
      {
        const typet& real_lhs_type=ns.follow(expr.type());
        if(real_lhs_type!=*override_type)
          init_expr=typecast_exprt(expr,*override_type);
      }
      init_expr=dereference_exprt(init_expr,init_expr.type().subtype());
        
      gen_nondet_init(init_expr,init_code,symbol_table,
                      recursion_set,false,"",false,create_dynamic_objects);
    }
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

    bool is_array=has_prefix(id2string(struct_type.get_tag()),"java::array[");

    for(const auto & component : components)
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

        bool _is_sub = name[0]=='@';
#if 0	
        irep_idt _class_identifier=
          _is_sub?(class_identifier.empty()?struct_tag:class_identifier):"";
#endif

        if((!_is_sub) && is_array)
          break;

        gen_nondet_init(me, init_code, symbol_table, recursion_set,
                        _is_sub, class_identifier, false, create_dynamic_objects);
      }
    }
    if(is_array)
      gen_nondet_array_init(expr,init_code,symbol_table,recursion_set,create_dynamic_objects);
    recursion_set.erase(struct_tag);
  }
  else
  {
    side_effect_expr_nondett se=side_effect_expr_nondett(type);

    code_assignt code(expr, se);
    init_code.copy_to_operands(code);
  }
}

// Borrowed from java_bytecode_convert.cpp -- todo find a sensible place to factor this.
static constant_exprt as_number(const mp_integer value, const typet &type)
{
  const unsigned int java_int_width(type.get_unsigned_int(ID_width));
  const std::string significant_bits(integer2string(value, 2));
  std::string binary_width(java_int_width - significant_bits.length(), '0');
  return constant_exprt(binary_width += significant_bits, type);
}  

void gen_nondet_array_init(const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  std::set<irep_idt> &recursion_set,
  bool create_dynamic_objects)
{
  namespacet ns(symbol_table);
  const typet &type=ns.follow(expr.type());
  
  const struct_typet &struct_type=to_struct_type(type);
  const auto &components=struct_type.components();

  assert(expr.type().id() == ID_symbol);
  const typet &element_type=static_cast<const typet &>(expr.type().find(ID_C_element_type));
    
  const struct_union_typet::componentt *clength=0, *cdata=0;
  for(const auto & component : components)
  {
    if(component.get_name()=="length")
      clength=&component;
    else if(component.get_name()=="data")
      cdata=&component;
  }

  assert(clength && cdata);

  const int max_nondet_array_length=5;
  auto max_length_expr=as_number(5,clength->type());
  exprt length_field_expr=member_exprt(expr,"length",clength->type());

  typet allocate_type;
  
  if(create_dynamic_objects)
  {
    // Initialise array with some undetermined length:
    gen_nondet_init(length_field_expr,init_code,symbol_table,recursion_set,
                    false,irep_idt(),false,false);

    // Insert assumptions to bound its length:
    binary_relation_exprt assume1(length_field_expr,ID_ge,
                                  as_number(0, clength->type()));
    binary_relation_exprt assume2(length_field_expr,ID_le,
                                  max_length_expr);
    code_assumet assume_inst1(assume1);
    code_assumet assume_inst2(assume2);
    init_code.move_to_operands(assume_inst1);
    init_code.move_to_operands(assume_inst2);

    allocate_type=array_typet(element_type,length_field_expr);
  }
  else
  {
    // Initialise array to max length.
    code_assignt assign_length(length_field_expr,max_length_expr);
    init_code.move_to_operands(assign_length);
    allocate_type=array_typet(element_type,max_length_expr);    
  }

  // Allocate space for array elements:
  exprt data_field_expr=member_exprt(expr,"data",cdata->type());
  assert(allocate_object(data_field_expr,allocate_type,init_code,
                         symbol_table,create_dynamic_objects));

  // Emit init loop for(array_init_iter=0; array_init_iter!=array.length; ++array_init_iter)
  //                  init(array[array_init_iter]);
  symbolt &counter=new_tmp_symbol(symbol_table,"array_init_iter");
  counter.type=length_field_expr.type();
  exprt counter_expr=counter.symbol_expr();
  
  init_code.copy_to_operands(
    code_assignt(counter_expr,as_number(0, clength->type())));

  std::string head_name=as_string(counter.base_name)+"_header";
  code_labelt init_head_label(head_name,code_skipt());
  code_gotot goto_head(head_name);

  init_code.move_to_operands(init_head_label);
  
  std::string done_name=as_string(counter.base_name)+"_done";
  code_labelt init_done_label(done_name,code_skipt());
  code_gotot goto_done(done_name);

  code_ifthenelset done_test;
  done_test.cond()=equal_exprt(counter_expr,length_field_expr);
  done_test.then_case()=goto_done;

  init_code.move_to_operands(done_test);

  exprt arraycellref=dereference_exprt(
    plus_exprt(data_field_expr,counter_expr,data_field_expr.type()),
    data_field_expr.type().subtype());

  bool must_dynamically_allocate=create_dynamic_objects ||
    element_type.id()==ID_pointer;
  gen_nondet_init(arraycellref,init_code,symbol_table,recursion_set,
                  false,irep_idt(),false,must_dynamically_allocate,
                  /*override_type=*/&element_type);

  code_assignt incr(counter_expr,
                    plus_exprt(counter_expr,
                               as_number(1, clength->type())));

  init_code.move_to_operands(incr);
  init_code.move_to_operands(goto_head);
  init_code.move_to_operands(init_done_label);
  
}
}

/*******************************************************************\

Function: gen_nondet_init

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  bool skip_classid,
  bool create_dynamic_objects)
{
  std::set<irep_idt> recursion_set;
  gen_nondet_init(expr, init_code, symbol_table, recursion_set, false, "", skip_classid, create_dynamic_objects);
}

/*******************************************************************\

Function: new_tmp_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbolt &new_tmp_symbol(symbol_tablet &symbol_table, const std::string& prefix)
{
  static int temporary_counter=0;

  auxiliary_symbolt new_symbol;
  symbolt *symbol_ptr;

  do
  {
    new_symbol.name=prefix+"$"+i2string(++temporary_counter);
    new_symbol.base_name=new_symbol.name;
    new_symbol.mode=ID_java;
  } while(symbol_table.move(new_symbol, symbol_ptr));

  return *symbol_ptr;
}

/*******************************************************************\

Function: get_nondet_bool

  Inputs: Desired type (C_bool or plain bool)

 Outputs: nondet expr of that type

 Purpose:

\*******************************************************************/

exprt get_nondet_bool(const typet& type) {
  // We force this to 0 and 1 and won't consider
  // other values.
  return typecast_exprt(side_effect_expr_nondett(bool_typet()), type);
}

/*******************************************************************\

Function: object_factory

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt object_factory(
  const typet &type,
  code_blockt &init_code,
  bool allow_null,
  symbol_tablet &symbol_table)
{
  if(type.id()==ID_pointer)
  {
    symbolt &aux_symbol=new_tmp_symbol(symbol_table);
    aux_symbol.type=type.subtype();
    aux_symbol.is_static_lifetime=true;

    exprt object=aux_symbol.symbol_expr();
    
    const namespacet ns(symbol_table);
    gen_nondet_init(object, init_code, symbol_table);

    // todo: need to pass null, possibly
    return address_of_exprt(object);
  }
  else if(type.id()==ID_c_bool)
  {
    // We force this to 0 and 1 and won't consider
    // other values.
    return get_nondet_bool(type);
  }
  else
    return side_effect_expr_nondett(type);
}

