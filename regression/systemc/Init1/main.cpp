#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../masc.h"

typedef sc_uint<1> uint1_t;
typedef sc_uint<2> uint2_t;

int main(int argc, char *argv[]) 
{
  uint1_t w(0);
  uint1_t x(1);
  x = uint1_t(0);
  assert(x == w);
  x = 1;
  uint2_t y = 1;
  uint2_t z = x;
  
  assert(y == z);

  return 0;
}

