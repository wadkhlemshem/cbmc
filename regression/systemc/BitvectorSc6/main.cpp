#include <assert.h>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"

int main(int argc, char** argv)
{
  sc_uint<4> x(15);
  sc_uint<4> z(9);
  sc_uint<2> y(0);
  x.range(2,1) = y;
  assert(x == z);

  return 0;
}
