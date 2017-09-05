/*******************************************************************\

Module: Dominators

Author: Georg Weissenbacher, georg@weissenbacher.name

\*******************************************************************/

/// \file
/// Dominators

#include "natural_loops.h"

void show_natural_loops(
  const goto_functionst &goto_functions,
  std::ostream &out)
{
  forall_goto_functions(it, goto_functions)
  {
   out << "*** " << it->first << '\n';

    natural_loopst natural_loops;
    natural_loops(it->second.body);
    natural_loops.output(out);

    out << '\n';
  }
}
