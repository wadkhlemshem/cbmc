#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../tuple.h"

typedef sc_uint<1> uint1_t;
typedef sc_uint<2> uint2_t;

int main(int argc, char *argv[]) 
{
  uint1_t a(1);
  uint2_t b = 1;
  //b = 1;
  uint2_t c; // = a;
  c = a;
  
  assert(b == c);

  return 0;
}

