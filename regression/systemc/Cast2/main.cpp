#include <cassert>

class myclass
{
  int x;
public:
  myclass(int _x) : x(_x) {}
  operator int () { return x; }  
};


int main(int argc, char *argv[]) 
{
  int y;
  myclass a(y);
  int z = (int)a;
  
  assert(y == z);

  return 0;
}

