#include <cassert>

class myclass
{
  int x;
public:
  myclass(int _x) : x(_x) {}
  operator signed int () { return x; }  
  // operator int () { return x+1; }  // not allowed to overload both
};


int main(int argc, char *argv[]) 
{
  int y;
  myclass a(y);
  int z = (int)a;
  
  assert(y == z);

  return 0;
}

