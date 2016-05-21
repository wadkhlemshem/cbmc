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

  x = 42; y = 69;

#ifndef __CPROVER__
  std::cout << p << std::endl;

  std::cout << x << "," << y << std::endl;
#endif
  assert(x==42);
  assert(y==69);

  tuple<bool,bool> q;
  q = tuple<bool,bool>(true,false);

#ifndef __CPROVER__
  std::cout << q << std::endl;
#endif
  
  bool foo, bar;

  tie(foo,bar) = q;

#ifndef __CPROVER__
  std::cout << foo << " " << bar << std::endl;
#endif
  assert(foo);
  assert(!bar);

  tuple<int> one;
  one = 69;
  
#ifndef __CPROVER__
  std::cout << one << std::endl;
#endif

  tie(x) = one;

#ifndef __CPROVER__
  std::cout << x << std::endl;
#endif
  assert(x==69);

#ifndef __CPROVER__
  tuple<int,std::string,int> three;
  three =   tuple<int,std::string,int>(42," does not equal ",69);

#ifndef __CPROVER__
  std::cout << three << std::endl;
#endif

  tuple<std::string,int,std::string,int> four;
  four =   tuple<std::string,int,std::string,int>("and ", 42," is less than ",69);

#ifndef __CPROVER__
  std::cout << four << std::endl;
#endif

  tuple<std::string,std::string> msg;
  msg = tuple<std::string,std::string>("hello","world");

#ifndef __CPROVER__
  std::cout << msg << std::endl;
#endif
  
  std::string xx,yy;
  tie(xx,yy) = tuple<std::string,std::string>("hello","world");

#ifndef __CPROVER__
  std::cout << xx << " " << yy << std::endl;
#endif
  assert(xx=="hello");
  assert(yy=="world");
#endif
  
}
