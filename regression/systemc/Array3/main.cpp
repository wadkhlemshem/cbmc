#include <assert.h>
#include "../masc.h"

#define FUNCTION

#ifdef FUNCTION
void check(array<int, 4> &y)
{
  assert(y[0] == 0);
  assert(y[3] == 3);
}
#endif

int main(void) {
  array<int, 4> x;

  for (int i=0; i<4; i++) {
    x[i] = i;
  }

  assert(x[0] == 0);
  assert(x[3] == 3);

#ifdef FUNCTION
  check(x); //this doesn't work
#else
  array<int, 4> &y = x; //this works
  assert(y[0] == 0);
  assert(y[3] == 3);
#endif 

  return 0;
}
