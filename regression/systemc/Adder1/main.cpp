//#define IO

#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../tuple.h"

#define K 2 //4 //8
#define W 2 //8 //32

#ifdef IO
#include <iostream>
#include <bitset>
#endif

typedef unsigned int uint;
#define W 2 //32
#define K 2 //8

typedef sc_uint<1> uint1_t;
typedef sc_uint<W+1> uint33_t;
typedef sc_uint<K*W> uint256_t;
typedef sc_uint<K*W+1> uint257_t;

// IMPL: a 32b-at-a-time adder

tuple<uint1_t, uint256_t> add256_impl(uint256_t a, uint256_t b)
{
  uint33_t p_sum(0); // = 0; //TODO
  uint256_t result;

  uint i;
  for(i=0; i<K; i++)
  {
    p_sum += (uint33_t)a.range(i*W+(W-1),i*W).to_uint() + b.range(i*W+(W-1),i*W); //.to_uint();
    result.range(i*W+(W-1),i*W) = p_sum.range((W-1),0); //.to_uint();
    p_sum >>= W;
  }
  return tuple<uint1_t, uint256_t> ((uint1_t)p_sum[0], result);
}

// SPEC: a biguint adder

tuple<uint1_t,uint256_t> bigadd (uint256_t a, uint256_t b) {
  uint257_t result = a + b; 
  return tuple<uint1_t,uint256_t> ((uint1_t)result[K*W], result.range(K*W-1,0));
}

int main(int argc, char *argv[]) 
{
  uint256_t a(15), b(15);
  tuple<uint1_t,uint256_t> spec_r, impl_r;

  spec_r = bigadd(a,b);
  impl_r = add256_impl(a,b);

#ifdef IO
  std::cout << "spec_r: " << spec_r << std::endl;
  std::cout << "impl_r: " << impl_r << std::endl;
#endif

  assert(spec_r == impl_r);

  return 0;
}

