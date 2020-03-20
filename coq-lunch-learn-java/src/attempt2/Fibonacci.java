package attempt2;

public class Fibonacci {
  public final int num;
  public final int seqPosition;

  private Fibonacci(int num, int seqPosition){
    this.num = num;
    this.seqPosition = seqPosition;
  }

  public static Fibonacci Fib1(){
    return new Fibonacci(1, 1);
  }

  public static Fibonacci Fib2(){
    return new Fibonacci(1, 2);
  }

  public static Fibonacci FibAdd(Fibonacci a, Fibonacci b){
    if(a.seqPosition + 1 != b.seqPosition){
      throw new IllegalArgumentException("That's not how you add Fibbonacci numbers");
    }

    return new Fibonacci(a.num + b.num, b.seqPosition + 1);
  }


}
