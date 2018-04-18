int foo()
{
  return 42;
}

int bar(int x)
{
  if(x < foo())
  {
    return 1;
  }
  else
  {
    return 0;
  }
}
