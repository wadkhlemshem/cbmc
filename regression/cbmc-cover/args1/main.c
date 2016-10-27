int main(int argc, char** argv)
{
  __CPROVER_input("argv[1]", argv[1]);

  if(argv[1][0]=='A')
  {
    return 0;
  }
  return 1;
}
