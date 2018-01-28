public class Main {

  public static void main (String[] args) {
    Node n = new Node();
    n.newM();
  }

  static class Node {
    int e;
    Node n;
    static Node m;

    void newM() {
      m = new Node();
      String s="m="+m.e;
      assert("hello".equals(s));
    }
  }
}
