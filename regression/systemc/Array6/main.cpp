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
//  myarray<uint, 2> c; //with this, it works
  b[index] = val; //didn't work, because template needs to be elaborated
}

int main(void) {
  myarray<uint, 2> a;
  uint i;
  __CPROVER_assume(0<=i && i<=1);
  //a[i] = i; //works
  assign(a,i,i);

  assert(a[i] == i);

  return 0;
}
