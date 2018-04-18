class A {
  int foo() {
    return 41;
  }
}

public class Test {

  public boolean bar(A a, int x) {
    if (x < a.foo()) {
      return true;
    } else {
      return false;
    }
  }
}
