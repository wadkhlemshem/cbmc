/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/


#ifndef CPROVER_UTIL_JAVA_SOURCE_LOCATION_H
#define CPROVER_UTIL_JAVA_SOURCE_LOCATION_H

#include "<util/source_location.h>"

class java_source_locationt:public source_locationt
{
public:
  java_source_locationt()
  {
  }

  const irep_idt &get_case_number() const
  {
    return get(ID_switch_case_number);
  }

  const irep_idt &get_java_bytecode_index() const
  {
    return get(ID_java_bytecode_index);
  }

  const irep_idt &get_basic_block_covered_lines() const
  {
    return get(ID_basic_block_covered_lines);
  }

  void set_case_number(const irep_idt &number)
  {
    set(ID_switch_case_number, number);
  }

  void set_java_bytecode_index(const irep_idt &index)
  {
    set(ID_java_bytecode_index, index);
  }

  void set_basic_block_covered_lines(const irep_idt &covered_lines)
  {
    return set(ID_basic_block_covered_lines, covered_lines);
  }

protected:
  std::string as_string(bool print_cwd) const override;
};

#endif // CPROVER_UTIL_JAVA_SOURCE_LOCATION_H
