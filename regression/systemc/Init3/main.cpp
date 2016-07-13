#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../masc.h"

typedef sc_uint<1> uint1_t;
typedef sc_uint<2> uint2_t;
typedef sc_uint<3> uint3_t;

int main(int argc, char *argv[]) 
{
  uint2_t x(1);
  uint2_t y(3);
  uint3_t z; // = x+y; //TODO: fails non-deterministically!!!
//  z = x+y;
//  z = uint3_t(x+y);
  z = (uint3_t)x+y;
  uint3_t w(4);
  
  assert(z == w);

  return 0;
}

