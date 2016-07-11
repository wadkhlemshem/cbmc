#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../masc.h"

typedef sc_uint<1> uint1;
typedef sc_uint<17> uint17;
typedef sc_uint<32> uint32;
typedef sc_uint<33> uint33;

tuple<uint1, uint32> add256_impl(uint32 a, uint32 b)
{
    uint17 p_sum = 0;
    uint32 result;

    uint i;
    for(i=0; i<2; i++)
    {
        p_sum += (uint17)a.range(i*16+15,i*16) + b.range(i*16+15,i*16);
        result.range(i*16+15,i*16) = p_sum.range(15,0);
        p_sum >>= 16;
    }
    return tuple<uint1, uint32> ((uint1)p_sum[0], result);
}

tuple<uint1,uint32> bigadd (uint32 a, uint32 b)
{
  uint33 result = (uint33)a + b;
  return tuple<uint1,uint32> ((uint1)result[32], result.range(31,0));
}

//extern uint32 nondet();

int main (int argc, char *argv[]) {

  uint32 a, b; //correctly constrained nondet now default behaviour
  uint32 spec_r, impl_r;
  uint1 spec_c, impl_c;
  //a = nondet(); //__CPROVER_assume(a.val<2147483648u);
  //b = nondet(); //__CPROVER_assume(b.val<2147483648u);

  tie(spec_c,spec_r) = bigadd(a,b);
  tie(impl_c,impl_r) = add256_impl(a,b);

  impl_r += uint32(1); //make it fail
  
  assert((spec_c == impl_c) && (spec_r == impl_r));

  return 0;
}

