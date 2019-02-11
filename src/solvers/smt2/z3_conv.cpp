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

Function: z3_convt::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

literalt z3_convt::convert(const exprt &expr)
{
  assert(expr.type().id()==ID_bool);

  // Three cases where no new handle is needed.

  if(expr.is_true())
    return const_literal(true);
  else if(expr.is_false())
    return const_literal(false);
  else if(expr.id()==ID_literal)
    return to_literal_expr(expr).get_literal();

  // Need a new handle

  literalt l(no_boolean_variables, false);
  no_boolean_variables++;

  solver.add(convert_literal(l) == convert_expr(expr));
  return l;
}

/*******************************************************************\

Function: z3_convt::convert_literal

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_literal(const literalt l) const
{
  if(l==const_literal(false))
    return context.bool_val(false);
  else if(l==const_literal(true))
    return context.bool_val(true);
  else
  {
    irep_idt lit_name=dstring("B"+i2string(l.var_no()));
    z3::expr lit(context);
    if (!exists(lit_name))
    {
      lit=context.bool_const(lit_name.c_str());
      store.push_back(lit);
      identifier_map[lit_name]=store.size() - 1;
    }
    lit=fetch(lit_name);
    if(l.sign())
      return !lit;
    else
      return lit;
  }
}

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
  else if(expr.id()==ID_floatbv_plus)
  {
    assert(expr.operands().size()>=2);
    assert(base_type_eq(expr.op0().type(), expr.op1().type(), ns));
    if(use_FPA_theory)
    {
      return z3::to_expr(context, Z3_mk_fpa_add(context,
                         convert_rounding_mode_FPA(expr.op2()),
                         convert_expr(expr.op0()),
                         convert_expr(expr.op1())));
    }
    else
    {
      return convert_expr(expr.op0())+convert_expr(expr.op1());
    }
  }
  else if(expr.id()==ID_typecast)
  {
    return convert_typecast(to_typecast_expr(expr));
  }
  else if(expr.id()==ID_floatbv_typecast)
  {
    return convert_floatbv_typecast(to_floatbv_typecast_expr(expr));
  }
  else if(expr.id()==ID_literal)
  {
    return convert_literal(to_literal_expr(expr).get_literal());
  }
  else if(expr.id()==ID_array_of)
  {
    return convert_array_of(to_array_of_expr(expr));
  }
  else if(expr.id() == ID_array)
  {
    return convert_array(to_array_expr(expr));
  }
  else if(expr.id()==ID_index)
  {
    return convert_index(to_index_expr(expr));
  }
  else if(expr.id()==ID_with)
  {
    return convert_with(to_with_expr(expr));
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

/*******************************************************************\

Function: z3_convt::convert_rounding_mode_FPA

  Inputs: The expression representing the rounding mode.

 Outputs: z3_expression

 Purpose: Converting a constant or symbolic rounding mode to SMT-LIB.
          Only called when use_FPA_theory is enabled

\*******************************************************************/

z3::expr z3_convt::convert_rounding_mode_FPA(const exprt &expr) const
{
  assert(use_FPA_theory);

  /* CProver uses the x86 numbering of the rounding-mode
   *   0 == FE_TONEAREST
   *   1 == FE_DOWNWARD
   *   2 == FE_UPWARD
   *   3 == FE_TOWARDZERO
   * These literal values must be used rather than the macros
   * the macros from fenv.h to avoid portability problems.
   */

  if(expr.id()==ID_constant)
  {
    const constant_exprt &cexpr=to_constant_expr(expr);

    mp_integer value=binary2integer(id2string(cexpr.get_value()), false);

    if(value==0)
      return z3::to_expr(context,Z3_mk_fpa_round_nearest_ties_to_even(context));
    else if(value==1)
      return z3::to_expr(context,Z3_mk_fpa_round_toward_negative(context));
    else if(value==2)
      return z3::to_expr(context,Z3_mk_fpa_round_toward_positive(context));
    else if(value==3)
      return z3::to_expr(context,Z3_mk_fpa_round_toward_zero(context));
    else
      INVALIDEXPR("Unknown constant rounding mode with value "+id2string(cexpr.get_value()));
  }
  else
  {
    std::size_t width=to_bitvector_type(expr.type()).get_width();

    // Need to make the choice above part of the model
    return z3::ite(context.bv_val(0,width)==convert_expr(expr), 
           z3::to_expr(context,Z3_mk_fpa_round_nearest_ties_to_even(context)), 
           z3::ite(context.bv_val(1,width)==convert_expr(expr),
           z3::to_expr(context,Z3_mk_fpa_round_toward_negative(context)),
           z3::ite(context.bv_val(2,width)==convert_expr(expr),
           z3::to_expr(context,Z3_mk_fpa_round_toward_positive(context)),
           z3::to_expr(context,Z3_mk_fpa_round_toward_zero(context)))));
  }
}

/*******************************************************************\

Function: z3_convt::convert_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_typecast(const typecast_exprt &expr) const
{
  assert(expr.operands().size()==1);
  const exprt &src=expr.op0();
  boolbv_widtht boolbv_width(ns);

  typet dest_type=ns.follow(expr.type());
  if(dest_type.id()==ID_c_enum_tag)
    dest_type=ns.follow_tag(to_c_enum_tag_type(dest_type));

  typet src_type=ns.follow(src.type());
  if(src_type.id()==ID_c_enum_tag)
    src_type=ns.follow_tag(to_c_enum_tag_type(src_type));

  z3::expr &&src_expr = convert_expr(src);

  if(dest_type.id()==ID_bool)
  {
    // this is comparison with zero
    if(src_type.id()==ID_signedbv ||
       src_type.id()==ID_unsignedbv ||
       src_type.id()==ID_c_bool ||
       src_type.id()==ID_fixedbv ||
       src_type.id()==ID_pointer)
    {
      return src_expr != convert_expr(gen_zero(src_type));
    }
    else if(src_type.id()==ID_floatbv)
    {
      if(use_FPA_theory)
      {
        return z3::to_expr(context,Z3_mk_not(context,
                           Z3_mk_fpa_is_zero(context,convert_expr(src))));
      }
      else
        return convert_expr(src)!=context.bv_val(0,boolbv_width(src.type()));
    }
    else
    {
      UNEXPECTEDCASE("TODO typecast1 "+src_type.id_string()+" -> bool");
    }
  }
  else if(dest_type.id()==ID_c_bool)
  {
    std::size_t to_width=boolbv_width(dest_type);
    return z3::ite(src_expr != convert_expr(gen_zero(src_type)),
      context.bv_val(1, to_width), context.bv_val(0, to_width));
  }
  else if(dest_type.id()==ID_signedbv ||
          dest_type.id()==ID_unsignedbv ||
          dest_type.id()==ID_c_enum ||
          dest_type.id()==ID_bv)
  {
    std::size_t to_width=boolbv_width(dest_type);

    if(src_type.id()==ID_signedbv || // from signedbv
       src_type.id()==ID_unsignedbv || // from unsigedbv
       src_type.id()==ID_c_bool ||
       src_type.id()==ID_c_enum ||
       src_type.id()==ID_bv)
    {
      std::size_t from_width=boolbv_width(src_type);

      if(from_width==to_width)
        return src_expr; // ignore
      else if(from_width<to_width) // extend
      {
        if(src_type.id()==ID_signedbv)
          return z3::sext(src_expr, to_width-from_width);
        else
        {
          return z3::zext(src_expr, to_width-from_width);
        }
      }
      else // chop off extra bits
      {
        return src_expr.extract(0, to_width);
      }
    }
    else if(src_type.id()==ID_bool) // from boolean to int
    {
      return z3::ite(src_expr, context.bv_val(1, to_width), context.bv_val(0, to_width));
    }
    else
    {
      UNEXPECTEDCASE("TODO typecast2 "+src_type.id_string()+" -> "+dest_type.id_string() + " src == " + from_expr(ns,"",src));
    }
  }
  else
  {
    UNEXPECTEDCASE("TODO typecast "+src_type.id_string()+" -> "+dest_type.id_string());
  }
  
}

/*******************************************************************\

Function: z3_convt::convert_floatbv_typecast

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_floatbv_typecast(const floatbv_typecast_exprt &expr) const
{
  const exprt &src=expr.op0();
  //const exprt &rounding_mode=expr.rounding_mode();
  const typet &src_type=src.type();
  const typet &dest_type=expr.type();

  if(dest_type.id()==ID_floatbv)
  {
    size_t to_width=boolbv_width(dest_type);
    if(src_type.id()==ID_floatbv)
    {
      size_t from_width=boolbv_width(src_type);
      // float to float

      /* ISO 9899:1999
       * 6.3.1.5 Real floating types
       * 1 When a float is promoted to double or long double, or a
       * double is promoted to long double, its value is unchanged.
       *
       * 2 When a double is demoted to float, a long double is
       * demoted to double or float, or a value being represented in
       * greater precision and range than required by its semantic
       * type (see 6.3.1.8) is explicitly converted to its semantic
       * type, if the value being converted can be represented
       * exactly in the new type, it is unchanged. If the value
       * being converted is in the range of values that can be
       * represented but cannot be represented exactly, the result
       * is either the nearest higher or nearest lower representable
       * value, chosen in an implementation-defined manner. If the
       * value being converted is outside the range of values that
       * can be represented, the behavior is undefined.
       */

      if(use_FPA_theory)
      {
        UNEXPECTEDCASE("TODO: convert floatbv float -> float with FPA");
      }
      else
      {
        floatbv_typet srct=to_floatbv_type(src_type);
        if (from_width==to_width)
          return convert_expr(src);
        if(from_width<to_width)
        {
          return z3::sext(convert_expr(src),to_width-from_width);
        }
        else
        {
          return convert_expr(src).extract(0,to_width);
        }
      }
    }
    else if(src_type.id()==ID_unsignedbv)
    {
      // unsigned to float

      /* ISO 9899:1999
       * 6.3.1.4 Real floating and integer
       * 2 When a value of integer type is converted to a real
       * floating type, if the value being converted can be
       * represented exactly in the new type, it is unchanged. If the
       * value being converted is in the range of values that can be
       * represented but cannot be represented exactly, the result is
       * either the nearest higher or nearest lower representable
       * value, chosen in an implementation-defined manner. If the
       * value being converted is outside the range of values that can
       * be represented, the behavior is undefined.
       */

      const floatbv_typet &dst=to_floatbv_type(dest_type);

      if(use_FPA_theory)
      {
        return z3::to_expr(context,Z3_mk_fpa_to_fp_unsigned(context,
                           convert_rounding_mode_FPA(expr.op1()),
                           convert_expr(src),
                           context.bv_sort(dst.get_e()+dst.get_f()+1)));
      }
      else
      {
        return convert_expr(src);
      }
    }
    else if(src_type.id()==ID_signedbv)
    {
      // signed to float
      UNEXPECTEDCASE("TODO floatbv typecast signed -> float");
    }
    else if(src_type.id()==ID_c_enum_tag)
    {
      // enum to float

      // We first convert to 'underlying type'
      UNEXPECTEDCASE("TODO floatbv typecast enum -> float");
    }
    else
      UNEXPECTEDCASE("TODO typecast11 "+src_type.id_string()+" -> "+dest_type.id_string());
  }
  else if(dest_type.id()==ID_signedbv)
  {
    UNEXPECTEDCASE("TODO typecast float -> signedbv");
  }
  else if(dest_type.id()==ID_unsignedbv)
  {
    UNEXPECTEDCASE("TODO typecast float -> unsignedbv");
  }
  else
  {
    UNEXPECTEDCASE("TODO typecast12 "+src_type.id_string()+" -> "+dest_type.id_string());
  }
}

/*******************************************************************\

Function: z3_convt::convert_array_of

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_array_of(const array_of_exprt &expr) const
{
  array_typet array_type=to_array_type(expr.type());
  z3::sort array_sort=convert_type(array_type.size().type());
  z3::expr what=convert_expr(expr.what());
  return z3::const_array(array_sort, what);
}

/*******************************************************************\

Function: z3_convt::convert_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_array(const array_exprt &expr) const
{
  array_typet array_type = to_array_type(expr.type());
  exprt zero=constant_exprt(integer2binary(mp_integer(0),64),array_type.subtype());
  z3::expr z3_array=convert_array_of(array_of_exprt(zero, array_type));
  int i=0;
  for (auto it=expr.operands().begin(); it!=expr.operands().end(); it++, i++)
  {
    z3_array = z3::store(z3_array, i, convert_expr(*it));
  }
  return z3_array;
}

/*******************************************************************\

Function: z3_convt::convert_index

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_index(const index_exprt &expr) const
{
  assert(expr.operands().size()==2);

  const typet &array_op_type=ns.follow(expr.array().type());

  if(array_op_type.id()==ID_array)
  {
    const z3::expr &array = convert_expr(expr.array());
    const z3::expr &index = convert_expr(expr.index());
    return z3::select(array, index);
  }
  else
    UNEXPECTEDCASE("index with unsupported array type: "+array_op_type.id_string());
}

/*******************************************************************\

Function: z3_convt::convert_with

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

z3::expr z3_convt::convert_with(const with_exprt &expr) const
{
  // get rid of "with" that has more than three operands

  assert(expr.operands().size()>=3);

  if(expr.operands().size()>3)
  {
    std::size_t s=expr.operands().size();

    // strip of the trailing two operands
    exprt tmp=expr;
    tmp.operands().resize(s-2);

    with_exprt new_with_expr;
    assert(new_with_expr.operands().size()==3);
    new_with_expr.type()=expr.type();
    new_with_expr.old()=tmp;
    new_with_expr.where()=expr.operands()[s-2];
    new_with_expr.new_value()=expr.operands()[s-1];

    // recursive call
    return convert_with(new_with_expr);
  }
  const typet &expr_type=ns.follow(expr.type());

  if(expr_type.id()==ID_array)
  {
    const z3::expr &array = convert_expr(expr.old());
    const z3::expr &index = convert_expr(expr.where());
    const z3::expr &value = convert_expr(expr.new_value());
    return z3::store(array, index, value);
  }
  else
  {
    UNEXPECTEDCASE("TODO convert_with: "+std::string(expr_type.id().c_str())+" "+from_expr(ns,"",expr)+"\n");
  } 
}

/*******************************************************************\

Function: z3_convt::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt z3_convt::l_get(literalt l) const
{
  if(l.is_true()) return tvt(true);
  if(l.is_false()) return tvt(false);
  z3::model model=solver.get_model();
  z3::expr res=model.eval(convert_literal(l));
  if (res.is_true())
    return tvt(true);
  else if (res.is_false())
    return tvt(false);
  else
    return tvt(tvt::unknown());
}

/*******************************************************************\

Function: z3_convt::get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt z3_convt::get(const exprt &expr) const
{
  z3::model model=solver.get_model();
  const z3::expr &e = model.eval(convert_expr(expr).simplify(params),true).simplify(params);
  return z3_convt::convert_z3_expr(e, expr.type());
}

/*******************************************************************\

Function: z3_convt::convert_z3_expr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt z3_convt::convert_z3_expr(const z3::expr &expr, const typet &type) const
{
  if (expr.get_sort().is_array())
  {
    return convert_z3_array(expr, to_array_type(type));
  }
  switch(expr.kind())
  {
    case Z3_NUMERAL_AST:
    case Z3_APP_AST:
    {
      switch(expr.decl().decl_kind())
      {
        case Z3_OP_TRUE:
        {
          return true_exprt();
        }
        case Z3_OP_FALSE:
        {
          return false_exprt();
        }
        case Z3_OP_BNUM:
        {
          std::size_t width=boolbv_width(type);
          mp_integer value=mp_integer(expr.get_decimal_string(width).c_str());
          if(type.id()==ID_bv ||
             type.id()==ID_signedbv ||
             type.id()==ID_unsignedbv ||
             type.id()==ID_c_enum ||
             type.id()==ID_c_bool)
          {
            return from_integer(value, type);
          }
          else if(type.id()==ID_c_enum_tag)
          {
            return from_integer(value,
                        ns.follow_tag(to_c_enum_tag_type(type)));
          }
          else if(type.id()==ID_fixedbv ||
                  type.id()==ID_floatbv)
          {
            return constant_exprt(integer2binary(value,width),type);
          }
          else if(type.id()==ID_incomplete_c_enum ||
                  type.id()==ID_c_bit_field)
          {
            UNEXPECTEDCASE("TODO: Conversion from Z3 expression to type "+type.id_string()+"\n");
          }
          else
          {
            UNEXPECTEDCASE("TODO: Conversion from Z3 expression to type "+type.id_string()+"\n");
          }
        }
        default:
          UNEXPECTEDCASE("Conversion from z3 expression type not yet implemented\n");
      }
    }
    case Z3_VAR_AST:
      UNEXPECTEDCASE("Z3_VAR_AST");
    case Z3_QUANTIFIER_AST:
      if (expr.is_exists())
      {
        UNEXPECTEDCASE("TODO: Conversion from Z3 EXISTS expression\n");
      }
      else if (expr.is_forall())
      {
        return true_exprt();
        UNEXPECTEDCASE("TODO: Conversion from Z3 FORALL expression\n");
      }
      else if (expr.is_lambda())
      {
        UNEXPECTEDCASE("TODO: Conversion from Z3 LAMBDA expression\n");
      }
      else
      {
        UNEXPECTEDCASE("Not a quantifier!");
      }
    case Z3_SORT_AST:
      UNEXPECTEDCASE("Z3_SORT_AST");
    case Z3_FUNC_DECL_AST:
      UNEXPECTEDCASE("Z3_FUNC_DECL_AST");
    default:
      UNEXPECTEDCASE("Z3_UNKNOWN_AST");
  }
}

/*******************************************************************\

Function: z3_convt::convert_z3_array

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt z3_convt::convert_z3_array(const z3::expr &expr, const array_typet &array_type) const 
{
  switch(expr.kind())
  {
    case Z3_QUANTIFIER_AST:
      if (expr.is_lambda())
      {
        z3::expr body=expr.body();

        // "Evaluate" the value at each index, and copy to a new array's operands

        // size_t size=binary2integer(id2string(to_constant_expr(array_type.size()).get_value()), false).to_ulong();
        // exprt array=array_exprt(array_type);
        // for (size_t i=0; i<size; i++)
        // {
        //   z3::expr_vector dst(context);
        //   dst.push_back(context.bv_val(i,expr.get_sort().array_domain().bv_size()));
        //   array.copy_to_operands(convert_z3_expr(body.substitute(dst).simplify(), array_type.subtype()));
        // }

        return convert_z3_array(body, array_type);
      }
      else
      {
        UNEXPECTEDCASE("Unexpected quantifier in Z3 array expression\n");
      }
    case Z3_NUMERAL_AST:
    case Z3_APP_AST:
      switch (expr.decl().decl_kind())
      {
        case Z3_OP_BNUM:
        {
          const exprt &what=convert_z3_expr(expr,array_type.subtype());
          return array_of_exprt(what, array_type);           
        }
        case Z3_OP_CONST_ARRAY:
        {
          const exprt &what = convert_z3_expr(expr.arg(0),array_type.subtype());
          return array_of_exprt(what, array_type);
        }
        case Z3_OP_STORE:
        {
          const exprt &array = convert_z3_array(expr.arg(0), array_type);
          const exprt &index = convert_z3_expr(expr.arg(1), array_type.size().type());
          const exprt &value = convert_z3_expr(expr.arg(2), array_type.subtype());
          return with_exprt(array, index, value);
        }
        case Z3_OP_ITE:
        {
          const exprt &index = convert_z3_expr(expr.arg(0).arg(1), array_type.size().type());
          const exprt &value = convert_z3_expr(expr.arg(1), array_type.subtype());
          const exprt &array = convert_z3_array(expr.arg(2), array_type);
          return with_exprt(array, index, value);
        }
        default:
          UNEXPECTEDCASE("Conversion from Z3 array expression "+std::to_string(expr.decl().decl_kind())+" type not yet implemented\n");
      }
    default:
      UNEXPECTEDCASE("Conversion from Z3 array "+std::to_string(expr.kind())+" kind not yet implemented\n");
  }
}
