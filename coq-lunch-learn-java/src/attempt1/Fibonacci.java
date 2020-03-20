package attempt1;

public class Fibonacci {
  public final int num;

  private Fibonacci(int num){
    this.num = num;
  }

  public static Fibonacci Fib1(){
    return new Fibonacci(1);
  }

  public static Fibonacci FibAdd(Fibonacci a, Fibonacci b){
    return new Fibonacci(a.num + b.num);
  }
}
