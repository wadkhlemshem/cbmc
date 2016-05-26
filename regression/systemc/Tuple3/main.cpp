#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../masc.h"

typedef sc_uint<1> uint1_t;
typedef sc_uint<4> uint256_t;
typedef sc_uint<5> uint257_t;

tuple<uint1_t,uint256_t> impl (uint256_t c, uint256_t d) {
  uint257_t result = c+d+uint256_t(1);
  return tuple<uint1_t,uint256_t> ((uint1_t)result[4], result.range(3,0));
}

tuple<uint1_t,uint256_t> spec (uint256_t c, uint256_t d) {
  uint257_t result = c+d;
  return tuple<uint1_t,uint256_t> ((uint1_t)result[4], result.range(3,0));
}

int main(int argc, char *argv[]) 
{
  uint256_t a(15), b(14);
  tuple<uint1_t,uint256_t> spec_r, impl_r;

  spec_r = spec(a,b);
  impl_r = impl(b,a);

  assert(spec_r == impl_r);

  return 0;
}

