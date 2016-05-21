#include <assert.h>
#include "../masc.h"

typedef unsigned uint;

void assign(array<uint, 2> &b, uint index, uint val)
{
//  myarray<uint, 2> c; //with this, it works
  b[index] = val; //didn't work, because template needs to be elaborated
}

int main(void) {
  array<uint, 2> a;
  uint i;
  __CPROVER_assume(0<=i && i<=1);
  //a[i] = i; //works
  assign(a,i,i);

  assert(a[i] == i);

  return 0;
}
