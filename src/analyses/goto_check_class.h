/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#ifndef CPROVER_ANALYSES_GOTO_CHECK_CLASS_H
#define CPROVER_ANALYSES_GOTO_CHECK_CLASS_H

#include <util/expr_util.h>
#include <util/guard.h>
#include <util/namespace.h>
#include <util/options.h>

#include <analyses/local_bitvector_analysis.h>

class goto_checkt
{
public:
  goto_checkt(
    const namespacet &_ns,
    const optionst &_options):
    ns(_ns),
    local_bitvector_analysis(nullptr)
  {
    enable_bounds_check=_options.get_bool_option("bounds-check");
    enable_pointer_check=_options.get_bool_option("pointer-check");
    enable_memory_leak_check=_options.get_bool_option("memory-leak-check");
    enable_div_by_zero_check=_options.get_bool_option("div-by-zero-check");
    enable_signed_overflow_check=
      _options.get_bool_option("signed-overflow-check");
    enable_unsigned_overflow_check=
      _options.get_bool_option("unsigned-overflow-check");
    enable_pointer_overflow_check=
      _options.get_bool_option("pointer-overflow-check");
    enable_conversion_check=_options.get_bool_option("conversion-check");
    enable_undefined_shift_check=
      _options.get_bool_option("undefined-shift-check");
    enable_float_overflow_check=
      _options.get_bool_option("float-overflow-check");
    enable_simplify=_options.get_bool_option("simplify");
    enable_nan_check=_options.get_bool_option("nan-check");
    retain_trivial=_options.get_bool_option("retain-trivial");
    enable_assert_to_assume=_options.get_bool_option("assert-to-assume");
    enable_assertions=_options.get_bool_option("assertions");
    enable_built_in_assertions=_options.get_bool_option("built-in-assertions");
    enable_assumptions=_options.get_bool_option("assumptions");
    error_labels=_options.get_list_option("error-label");
  }

  typedef goto_functionst::goto_functiont goto_functiont;

  void goto_check(goto_functiont &goto_function, const irep_idt &mode);

  void collect_allocations(const goto_functionst &goto_functions);

protected:
  const namespacet &ns;
  local_bitvector_analysist *local_bitvector_analysis;
  goto_programt::const_targett t;

  void check_rec(
    const exprt &expr,
    guardt &guard,
    bool address,
    const irep_idt &mode);
  void check(const exprt &expr, const irep_idt &mode);

  void bounds_check(const index_exprt &expr, const guardt &guard);
  void div_by_zero_check(const div_exprt &expr, const guardt &guard);
  void mod_by_zero_check(const mod_exprt &expr, const guardt &guard);
  void undefined_shift_check(const shift_exprt &expr, const guardt &guard);
  void pointer_rel_check(const exprt &expr, const guardt &guard);
  void pointer_overflow_check(const exprt &expr, const guardt &guard);
  virtual void pointer_validity_check(
    const dereference_exprt &expr,
    const guardt &guard,
    const exprt &access_lb,
    const exprt &access_ub,
    const irep_idt &mode);
  void integer_overflow_check(const exprt &expr, const guardt &guard);
  void conversion_check(const exprt &expr, const guardt &guard);
  void float_overflow_check(const exprt &expr, const guardt &guard);
  void nan_check(const exprt &expr, const guardt &guard);

  virtual void do_function_call(const goto_programt::instructiont &, const irep_idt &mode);

  std::string array_name(const exprt &expr);

  void add_guarded_claim(
    const exprt &expr,
    const std::string &comment,
    const std::string &property_class,
    const source_locationt &,
    const exprt &src_expr,
    const guardt &guard);

  goto_programt new_code;
  typedef std::set<exprt> assertionst;
  assertionst assertions;

  void invalidate(const exprt &lhs);

  inline static bool has_dereference(const exprt &src)
  {
    return has_subexpr(src, ID_dereference);
  }

  bool enable_bounds_check;
  bool enable_pointer_check;
  bool enable_memory_leak_check;
  bool enable_div_by_zero_check;
  bool enable_signed_overflow_check;
  bool enable_unsigned_overflow_check;
  bool enable_pointer_overflow_check;
  bool enable_conversion_check;
  bool enable_undefined_shift_check;
  bool enable_float_overflow_check;
  bool enable_simplify;
  bool enable_nan_check;
  bool retain_trivial;
  bool enable_assert_to_assume;
  bool enable_assertions;
  bool enable_built_in_assertions;
  bool enable_assumptions;

  typedef optionst::value_listt error_labelst;
  error_labelst error_labels;

  typedef std::pair<exprt, exprt> allocationt;
  typedef std::list<allocationt> allocationst;
  allocationst allocations;
};

#endif // CPROVER_ANALYSES_GOTO_CHECK_CLASS_H
