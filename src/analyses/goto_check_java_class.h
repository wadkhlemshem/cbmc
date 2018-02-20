/*******************************************************************\

Module: Program Transformation

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Program Transformation

#ifndef CPROVER_ANALYSES_GOTO_CHECK_JAVA_CLASS_H
#define CPROVER_ANALYSES_GOTO_CHECK_JAVA_CLASS_H

#include <analyses/goto_check.h>

class goto_check_javat : public goto_checkt
{
public:
  goto_check_javat(
    const namespacet &_ns,
    const optionst &_options)
  : goto_checkt(_ns, _options)
  {
  }

protected:
  void pointer_validity_check(
    const dereference_exprt &expr,
    const guardt &guard,
    const exprt &access_lb,
    const exprt &access_ub,
    const irep_idt &mode) override;

  void do_function_call(
    const goto_programt::instructiont &, const irep_idt &mode) override;

  void copy_source_location(
    goto_programt::targett dest,
    goto_programt::const_targett src) override;
};

#endif // CPROVER_ANALYSES_GOTO_CHECK_JAVA_CLASS_H
