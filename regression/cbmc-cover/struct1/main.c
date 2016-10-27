struct mystruct {
  int x;
  char y;
};

int main()
{
  struct mystruct s;
  __CPROVER_input("s", s);

  if(s.y=='A')
  {
    return 0;
  }
  return 1;
}
