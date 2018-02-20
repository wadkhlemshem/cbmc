/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_JAVA_SOURCE_LOCATION_H
#define CPROVER_UTIL_JAVA_SOURCE_LOCATION_H

#include <util/source_location.h>

class java_source_locationt:public source_locationt
{
public:
  java_source_locationt()
  {
  }

  std::string as_string() const
  {
    return as_string(false);
  }

  std::string as_string_with_cwd() const
  {
    return as_string(true);
  }

  const irep_idt &get_java_bytecode_index() const
  {
    return get(ID_java_bytecode_index);
  }

  void set_java_bytecode_index(const irep_idt &index)
  {
    set(ID_java_bytecode_index, index);
  }

protected:
  std::string as_string(bool print_cwd) const;
};

#endif // CPROVER_UTIL_JAVA_SOURCE_LOCATION_H
