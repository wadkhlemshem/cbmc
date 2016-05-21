#include <assert.h>
#include "../masc.h"

#define COPY

typedef unsigned uint;

#ifdef COPY
array<uint, 3> rev3u(array<uint, 3> x) {
  array<uint, 3> y;
  y[0] = x[2];
  y[1] = x[1];
  y[2] = x[0];
  return y;
}

#else

void rev3u(array<uint, 3> x, array<uint, 3> &y) {
  y[0] = x[2];
  y[1] = x[1];
  y[2] = x[0];
}
#endif

extern bool arbb();
extern uint arbu();

int main(void) {
  array<bool, 4> arrb;

  for (int i=0; i<4; i++) {
    bool cond = (i%2 == 0);
    arrb[i] = cond;
  }

  assert(arrb[0] == true);
  assert(arrb[1] == false);
  assert(arrb[2] == true); //problem: fails without constant propagation
  assert(arrb[3] == false);

  array<uint, 3> arru;
  for (int i=0; i<3; i++) {
    arru[i] = arbu();
  }

  array<uint, 3> arru2;
#ifdef COPY
  arru2 = rev3u(arru); //problem: copy constructor refuses to copy array (solved)
                       //new problem: byte_extract_little_endian ignored
#else
  rev3u(arru,arru2);
#endif
  assert (arru2[0] == arru[2]);
  assert (arru2[1] == arru[1]);
  assert (arru2[2] == arru[0]);

  return 0;
}
