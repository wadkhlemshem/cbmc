public class Main {
  public enum MyEnum {
    A, B, C };

  public static MyEnum e = MyEnum.B;

  public static void main(String[] args) {
    int i = 0;
    switch(e) {
    case A: i = 2; break;
    case B: i = 4; break;
    case C: i = 8; break;
    }
    assert(i == 4);
  }
}
