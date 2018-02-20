/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#include <analyses/goto_check_java.h>

void goto_checkt::pointer_validity_check(
  const dereference_exprt &expr,
  const guardt &guard,
  const exprt &access_lb,
  const exprt &access_ub,
  const irep_idt &mode)
{
  if(!enable_pointer_check)
    return;

  const exprt &pointer=expr.op0();
  const pointer_typet &pointer_type=
    to_pointer_type(ns.follow(pointer.type()));

  assert(base_type_eq(pointer_type.subtype(), expr.type(), ns));

  local_bitvector_analysist::flagst flags=
    local_bitvector_analysis->get(t, pointer);

  const typet &dereference_type=pointer_type.subtype();

  // For Java, we only need to check for null
  if(flags.is_unknown() || flags.is_null())
  {
    notequal_exprt not_eq_null(pointer, null_pointer_exprt(pointer_type));

    add_guarded_claim(
      not_eq_null,
      "reference is null",
      "pointer dereference",
      expr.find_source_location(),
      expr,
      guard);
  }
}

void goto_check_javat::do_function_call(const goto_programt::instructiont &i, const irep_idt &mode)
{
  const code_function_callt &code_function_call=
    to_code_function_call(i.code);

  // for Java, need to check whether 'this' is null
  // on non-static method invocations
  if(enable_pointer_check &&
     !code_function_call.arguments().empty() &&
     code_function_call.function().type().id()==ID_code &&
     to_code_type(code_function_call.function().type()).has_this())
  {
    exprt pointer=code_function_call.arguments()[0];

    local_bitvector_analysist::flagst flags=
      local_bitvector_analysis->get(t, pointer);

    if(flags.is_unknown() || flags.is_null())
    {
      notequal_exprt not_eq_null(
        pointer,
        null_pointer_exprt(to_pointer_type(pointer.type())));

      add_guarded_claim(
        not_eq_null,
        "this is null on method invocation",
        "pointer dereference",
        i.source_location,
        pointer,
        guardt());
    }
  }

  forall_operands(it, code_function_call)
    check(*it, mode);

  // the call might invalidate any assertion
  assertions.clear();
}

void goto_check_javat::copy_source_location(
  goto_programt::targett dest, goto_programt::const_targett src)
{
  goto_checkt::copy_source_location(dest, src);
  java_source_locationt &dest_loc =
    static_cast<java_source_locationt &>(dest->source_location);
  java_source_locationt &src_loc =
    static_cast<java_source_locationt &>(src->source_location);

  if(!src_loc.get_java_bytecode_index().empty())
  {
    dest_loc.set_java_bytecode_index(
      src_loc.get_java_bytecode_index());
  }
}
