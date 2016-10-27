int main(int argc, char** argv)
{
  char a[10];
  __CPROVER_input("a[0]", a[0]);

  if(a[0]=='A')
  {
    return 0;
  }
  return 1;
}
