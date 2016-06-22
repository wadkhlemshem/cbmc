#include <cassert>

class myclass
{
  int x;
public:
  myclass(int _x) : x(_x) {}
  operator int () { return x+1; }  
};


int main(int argc, char *argv[]) 
{
  int y;
  myclass a(y);
  int z = a; // (int)
  
  assert(y+1 == z);

  return 0;
}

