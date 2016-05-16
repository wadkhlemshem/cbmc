#include <assert.h>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"

int main(int argc, char** argv)
{
  sc_uint<4> x(15);
  sc_uint<4> y;
  y = 13;
  x[1] = 0; 
  assert(x == y);

  return 0;
}
