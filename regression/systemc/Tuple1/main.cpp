#include <cassert>
#include "../masc.h"

#ifndef __CPROVER__
#include <string>
#endif

int main(int argc, char** argv)
{
  tuple<int,int> p;
  int x=0, y=0;

  p = tuple<int,int>(1,2);

#ifndef __CPROVER__
  std::cout << p << std::endl;
#endif
  
  p = tuple<int,int>(3,4);

#ifndef __CPROVER__
  std::cout << p << std::endl;

  std::cout << x << "," << y << std::endl;
#endif
  assert(x==0);
  assert(y==0);

  tie(x,y) = p;

#ifndef __CPROVER__
  std::cout << x << "," << y << std::endl;
#endif
  assert(x==3);
  assert(y==4);
  
  p = tuple<int,int>(5,6);

#ifndef __CPROVER__
  std::cout << p << std::endl;

  std::cout << x << "," << y << std::endl;
#endif
  assert(x==3);
  assert(y==4);

}
