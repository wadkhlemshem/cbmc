#include <cassert>
#include "../systemc_util.cpp"
#include "../sc_uint_base.cpp"
#include "../sc_uint.h"
#include "../masc.h"

typedef sc_uint<8> ui8;

int main(int argc, char *argv[]) {

  ui8 a;
  ui8 b;
  ui8 result;

  result = ui8(152);
  result += ui8(128);

  // should be true
  assert (result.to_uint() == 24);

  return 0;
}
