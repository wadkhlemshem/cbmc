#include <assert.h>

typedef unsigned uint;

template <class T, uint m>
class myarray {

  T elt[m];

public:
  T& operator[] (int idx) {
    return elt[idx];
  }
};

void assign(myarray<uint, 2> &b, uint index, uint val)
{
  b[index] = val;
}

int main(void) {
  myarray<uint, 2> a;
  uint i;
  __CPROVER_assume(0<=i && i<=1);
  assign(a,i,i);

  assert(a[i] == i);

  return 0;
}
