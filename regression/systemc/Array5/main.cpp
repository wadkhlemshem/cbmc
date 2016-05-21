#include <assert.h>
#include "../masc.h"

typedef unsigned uint;

int main(void) {
  array<uint, 2> a;
  uint i;
  __CPROVER_assume(0<=i && i<=1);
  a[i] = i;

  assert(a[i] == i);

  return 0;
}
