int foo()
{
  return 41;
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
