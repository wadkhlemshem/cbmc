#include <assert.h>
#include "../masc.h"

int main(void) {
  array<int, 4> x;

  for (int i=0; i<4; i++) {
    x[i] = i;
  }

  assert(x[0] == 0);
  assert(x[3] == 3);

  array<int, 4> y = x; //copy constructor does not typecheck
  assert(y[0] == 0);
  assert(y[3] == 3);
 
  return 0;
}
