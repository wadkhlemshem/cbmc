/*******************************************************************\

Module: Z3 C++ API Backend

Author(s): Johanan Wahlang, wadkhlemshem@gmail.com
           Manasij Mukherjee, manasij7479@gmail.com

\*******************************************************************/

#include <cassert>

#include <util/arith_tools.h>
#include <util/expr_util.h>
#include <util/std_types.h>
#include <util/std_expr.h>
#include <util/i2string.h>
#include <util/fixedbv.h>
#include <util/pointer_offset_size.h>
#include <util/ieee_float.h>
#include <util/base_type.h>
#include <util/string2int.h>

#include <ansi-c/string_constant.h>

#include <langapi/language_util.h>

#include <solvers/flattening/boolbv_width.h>
#include <solvers/flattening/flatten_byte_operators.h>
#include <solvers/flattening/c_bit_field_replacement_type.h>
#include <solvers/floatbv/float_bv.h>

#include "z3_conv.h"

#include <stdlib.h>
#include <sstream>
#include <bitset>
#include <string>

// Mark different kinds of error condition
// General
#define UNREACHABLE throw "Supposidly unreachable location reached"
#define PARSERERROR(S) throw S

// Error checking the expression type
#define INVALIDEXPR(S) throw "Invalid expression: " S

// Unexpected types and other combination not implemented and not expected to be needed
#define UNEXPECTEDCASE(S) throw "Unexpected case: " S

// General todos
#define TODO(S) throw "TODO: " S

/*******************************************************************\

Function: z3_convt::convert_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_expr(const exprt &expr) const
{
  if(expr.id() == ID_constant)
  {
    return convert_constant(to_constant_expr(expr));
  }
  else if(expr.id()==ID_symbol)
  {
    return convert_identifier(to_symbol_expr(expr).get_identifier(),
                              ns.follow(expr.type()));
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    irep_idt id=expr.get(ID_identifier);
    assert(id!=irep_idt());
    return convert_identifier(id,ns.follow(expr.type()));
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);
    return ite(convert_expr(expr.op0()),
               convert_expr(expr.op1()),
               convert_expr(expr.op2()));
  }
  else if(expr.id()==ID_and)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()>=2);
    z3::expr result = convert_expr(expr.op0());
    for (unsigned int i = 1; i < expr.operands().size(); ++i)
    {
      result = result && convert_expr(expr.operands()[i]);
    }
    return result;
  }
  else if(expr.id()==ID_or)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()>=2);
    z3::expr result = convert_expr(expr.op0());
    for (unsigned int i = 1; i < expr.operands().size(); ++i)
    {
      result = result || convert_expr(expr.operands()[i]);
    }
    return result;
  }
  else if(expr.id()==ID_xor)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()>=2);
    z3::expr result = convert_expr(expr.op0());
    for (unsigned int i = 1; i < expr.operands().size(); ++i)
    {
      result = result ^ convert_expr(expr.operands()[i]);
    }
    return result;
  }
  else if(expr.id()==ID_implies)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()==2);

    return implies(convert_expr(expr.op0()),
                   convert_expr(expr.op1()));
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.type().id()==ID_bool);
    assert(expr.operands().size()==1);
    return !convert_expr(expr.op0());;
  }
  else if(expr.id()==ID_equal)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           == convert_expr(expr.op1());
  }
  else if(expr.id()==ID_notequal)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           != convert_expr(expr.op1());
  }
  else if(expr.id()==ID_ieee_float_equal)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(),expr.op1().type(),ns));
    if(use_FPA_theory)
    {
      return z3::to_expr(context, Z3_mk_fpa_eq(context,
                         convert_expr(expr.op0()),
                         convert_expr(expr.op1())));
    }
    else
    {
      return convert_expr(expr.op0())==convert_expr(expr.op1());
    }
  }
  else if(expr.id()==ID_ieee_float_notequal)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(),expr.op1().type(),ns));
    if(use_FPA_theory)
    {
      return z3::to_expr(context, Z3_mk_not(context, 
                         Z3_mk_fpa_eq(context,
                         convert_expr(expr.op0()),
                         convert_expr(expr.op1()))));
    }
    else
      return convert_expr(expr.op0())!=convert_expr(expr.op1());
  }
  else if (expr.id()==ID_le)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           <= convert_expr(expr.op1());
  }
  else if (expr.id()==ID_lt)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           < convert_expr(expr.op1());
  }
  else if (expr.id()==ID_ge)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           >= convert_expr(expr.op1());
  }
  else if (expr.id()==ID_gt)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           > convert_expr(expr.op1());
  }
  else if(expr.id()==ID_forall)
  {
    return z3::forall(convert_expr(expr.op0()), convert_expr(expr.op1()));
  }
  else if(expr.id()==ID_exists)
  {
    return z3::exists(convert_expr(expr.op0()), convert_expr(expr.op1()));
  }
  else if(expr.id()==ID_unary_plus)
  {
    return convert_expr(expr.op0());
  }
  else if(expr.id()==ID_unary_minus)
  {
    assert(expr.operands().size()==1);
    if(expr.type().id()==ID_signedbv)
      return z3::to_expr(context, Z3_mk_bvneg(context,convert_expr(expr.op0())));
    else if(expr.type().id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        UNEXPECTEDCASE("TODO: Unary minus for floatbv with FPA theory");
      }
      else
      {
        return z3::to_expr(context, Z3_mk_bvneg(context,convert_expr(expr.op0())));
      }
    }
    else
    {
      UNEXPECTEDCASE("TODO: Unary minus for "+expr.type().id_string()+"\n");
    }
  }
  else if (expr.id()==ID_plus)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           + convert_expr(expr.op1());
  }
  else if (expr.id()==ID_minus)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           - convert_expr(expr.op1());
  }
  else if (expr.id()==ID_mult)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           * convert_expr(expr.op1());
  }
  else if (expr.id()==ID_div)
  {
    assert(expr.operands().size()==2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    return convert_expr(expr.op0())
           / convert_expr(expr.op1());
  }
  else
  {
    UNEXPECTEDCASE("TODO: convert type "+std::string(expr.id().c_str())+" "+ from_expr(ns,"",expr)+"\n");
  }
}

/*******************************************************************\

Function: z3_convt::convert_constant

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_constant(const constant_exprt &expr) const
{
  const typet &type=expr.type();
  if(type.id()==ID_bool)
  {
    if(expr.is_true())
      return context.bool_val(true);
    else
      return context.bool_val(false);
  }
  if(type.id()==ID_unsignedbv ||
     type.id()==ID_signedbv ||
     type.id()==ID_bv ||
     type.id()==ID_c_enum ||
     type.id()==ID_c_enum_tag ||
     type.id()==ID_c_bool ||
     type.id()==ID_incomplete_c_enum ||
     type.id()==ID_c_bit_field)
  {
    std::size_t width=boolbv_width(type);
    std::string value=integer2string(binary2integer(id2string(expr.get_value()),false));
    return context.bv_val(value.c_str(), width);
  }
  else if(type.id()==ID_fixedbv)
  {
    fixedbv_spect spec(to_fixedbv_type(type));
    std::string value=integer2string(binary2integer(id2string(expr.get_value()),false));
    return context.bv_val(value.c_str(), spec.width);
  }
  else if(type.id()==ID_floatbv)
  {
    const floatbv_typet &floatbv_type=to_floatbv_type(type);
    if(use_FPA_theory)
    {
      ieee_floatt v=ieee_floatt(expr);
      if(v.is_NaN())
      {
        UNEXPECTEDCASE("TODO: Conversion of NaN");
      }
      else if(v.is_infinity())
      {
        if(v.get_sign())
        {
          UNEXPECTEDCASE("TODO: Conversion of -oo");
        }
        else
        {
          UNEXPECTEDCASE("TODO: Conversion of oo");
        }
      }
      else
      {
        mp_integer binary=v.pack();
        std::string binaryString(integer2binary(v.pack(),v.spec.width()));
        UNEXPECTEDCASE("TODO: Conversion of floatbv with FPA");
      }
    }
    else
    {
      ieee_float_spect spec(floatbv_type);
      std::string value=integer2string(binary2integer(id2string(expr.get_value()),false));
      return context.bv_val(value.c_str(), spec.width());
    }
  }
  else if (type.id()==ID_integer)
  {
    return context.int_val(expr.get_value().c_str());
  }
  else if (type.id()==ID_pointer)
  {
    const irep_idt &value=expr.get(ID_value);
    if (value==ID_NULL)
    {
      return context.bv_val(0, boolbv_width(type));
    }
    else
    {
      UNEXPECTEDCASE("unknown pointer constant: "+id2string(value)+"\n");
    }
  }
  else
  {
    UNEXPECTEDCASE("TODO constant: "+std::string(type.id().c_str())+" "+from_expr(ns,"",expr)+"\n");
  }
}

/*******************************************************************\

Function: z3_convt::convert_type

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::sort z3_convt::convert_type(const typet &type) const
{
  if(type.id()==ID_bool)
  {
    return context.bool_sort();
  }
  else if(type.id()==ID_signedbv ||
          type.id()==ID_unsignedbv ||
          type.id()==ID_fixedbv ||
          type.id()==ID_floatbv ||
          type.id()==ID_verilog_signedbv ||
          type.id()==ID_verilog_unsignedbv ||
          type.id()==ID_bv ||
          type.id()==ID_c_bit_field ||
          type.id()==ID_c_bool)
  {
    size_t width = to_bitvector_type(type).get_width();
    return context.bv_sort(width);
  }
  else if(type.id()==ID_array)
  {
    const array_typet &array_type = to_array_type(type);
    const typet &array_index_type = array_type.size().type();    
    const typet &array_value_type = array_type.subtype();
    return context.array_sort(convert_type(array_index_type), convert_type(array_value_type));
  }
  else if(type.id()==ID_pointer)
  {
    size_t width=to_bitvector_type(type).get_width();
    if (width==0)
      return context.bv_sort(64);
    else
      return context.bv_sort(width);
  }
  else if(type.id()==ID_integer)
  {
    return context.int_sort();
  }
  else
  {
    UNEXPECTEDCASE("TODO: Type conversion for "+type.id_string()+"\n");
  }
}

/*******************************************************************\

Function: z3_convt::convert_identifier

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_identifier(const irep_idt &id, const typet &type) const
{
  assert(id!=irep_idt());
  if (!exists(id)) {
    z3::expr expr(context);
    expr = context.constant(id.c_str(), convert_type(type));
    store.push_back(expr);
    identifier_map[id] = store.size() - 1;
  }
  return fetch(id);
}
