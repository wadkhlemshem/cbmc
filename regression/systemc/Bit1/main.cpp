#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../masc.h"

typedef sc_uint<64> uint64;
typedef sc_uint<65> uint65;

int main (int argc, char *argv[])
{
  
  uint64 a(18446744073709551615ul);
#ifdef USE_BV
  uint65 b(1);
#else
  uint64 b(2);
#endif  

  b += a;
  
#ifdef USE_BV
  int pos=64;
#else
  int pos=0;
#endif  
  bool b64 = b[pos];
  assert(b64);

  return 0;
}

