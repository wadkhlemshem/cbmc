#include <assert.h>

int main(int argc, char** argv)
{
  __CPROVER_fixedbv[3][1] x;
  x = 0.5;
  __CPROVER_fixedbv[3][1] y;
  y = 1.0;
  __CPROVER_fixedbv[3][1] z;
  z = 1.5;
  __CPROVER_fixedbv[3][1] w = x+y;

  assert(z == w);

  return 0;
}
