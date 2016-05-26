#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"

typedef sc_uint<1> uint1_t;
typedef sc_uint<4> uint256_t;

void check()
{
#if 0
  uint1_t abc;
#endif

  uint1_t result;
  result.range(0,0) = result.range(0,0);

  uint1_t spec(0), impl(1);

  assert(impl == spec);
}

int main(int argc, char *argv[]) 
{
#if 1
  uint1_t abc;
#endif

  check();

  return 0;
}

