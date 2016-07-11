#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../masc.h"

#ifdef USE_BV
typedef sc_uint<128> uint128;
typedef sc_uint<64> uint64;
#else
typedef sc_uint<64> uint128;
typedef sc_uint<32> uint64;
#endif

int main (int argc, char *argv[])
{
  
#ifdef USE_BV
  uint64 a(18446744073709551615ul);
  int left=127;
  int right=64;
#else
  uint64 a(4294967295u);
  int left=63;
  int right=32;
#endif
  uint128 b(0);

  b.range(left-1,right-1) = a;

  uint64 c = b.range(left,right);
  a >>= 1; //comment to make it fail
  assert(c == a);

  return 0;
}

