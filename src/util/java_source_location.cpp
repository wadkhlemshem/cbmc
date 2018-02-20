/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "java_source_location.h"

#include <ostream>

#include "file_util.h"

/// \par parameters: print_cwd, print the absolute path to the file
std::string source_locationt::as_string(bool print_cwd) const
{
  std::string dest = source_locationt::as_string(print_cwd);

  if(!bytecode.empty())
  {
    if(dest!="")
      dest+=' ';
    dest+="bytecode-index "+id2string(bytecode);
  }

  return dest;
}
