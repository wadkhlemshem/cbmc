/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_JAVA_OBJECT_FACTORY_H
#define CPROVER_JAVA_OBJECT_FACTORY_H

#include <util/std_code.h>
#include <util/symbol_table.h>

exprt object_factory(
  const typet &type,
  code_blockt &init_code,
  bool allow_null,
  symbol_tablet &symbol_table);

void gen_nondet_init(
  const exprt &expr,
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  bool skip_classid = false,
  bool create_dynamic_objects = false,
  bool assume_non_null = false);

exprt get_nondet_bool(const typet&);

symbolt &new_tmp_symbol(
  symbol_tablet &symbol_table,
  const std::string& prefix = "tmp_object_factory");

#endif
