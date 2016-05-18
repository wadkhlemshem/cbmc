#include <assert.h>

int main(int argc, char** argv)
{
  __CPROVER::fixedbv<3,1> x;
  x = 0x2;
  __CPROVER::fixedbv<3,1> y;
  y = 0x1;
  __CPROVER::fixedbv<3,1> z;
  z = 0;
  __CPROVER::fixedbv<3,1> w = x+y;

  assert(z == w);

  return 0;
}
