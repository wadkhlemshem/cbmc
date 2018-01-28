public class Main {
  public enum MyEnum {
    A, B, C };

  public static void main(String[] args) {
    assert(MyEnum.B.ordinal() == 1);
  }
}
