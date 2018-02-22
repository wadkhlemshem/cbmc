/*******************************************************************\

Module: Expressions in JSON

Author: Peter Schrammel

\*******************************************************************/

/// \file
/// Expressions in JSON

#include <util/json_expr_java.h>

json_objectt json(const java_source_locationt &location)
{
  json_objectt result = json(static_cast<const source_locationt &>(location));

  if(!location.get_java_bytecode_index().empty())
    result["bytecodeIndex"]=
      json_stringt(id2string(location.get_java_bytecode_index()));

  return result;
}
