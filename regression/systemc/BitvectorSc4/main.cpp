#include <assert.h>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"

int main(int argc, char** argv)
{
  sc_uint<2> x(1);
  assert(x[0]);
  bool b = x[1];
  assert(!b);

  return 0;
}
