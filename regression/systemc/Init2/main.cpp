#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../tuple.h"

typedef sc_uint<1> uint1_t;
typedef sc_uint<2> uint2_t;

int main(int argc, char *argv[]) 
{
  uint1_t x(1);
  x = uint1_t(0);
  x = 1;
  uint2_t v(1);
  uint2_t y = v; //uint2_t(1);
  uint2_t z = x;
  
  assert(y == z);

  return 0;
}

