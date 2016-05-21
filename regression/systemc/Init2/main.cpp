#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../masc.h"

typedef sc_uint<1> uint1_t;
typedef sc_uint<2> uint2_t;

int main(int argc, char *argv[]) 
{
  uint2_t y = uint2_t(3);
  uint2_t s(3);
  uint2_t z = s;
  
  assert(y == z);

  return 0;
}

