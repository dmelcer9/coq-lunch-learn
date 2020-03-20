package attempt2;

public class Main {
  public static void main(String[] args){
    Fibonacci f1 = Fibonacci.Fib1();
    Fibonacci f2 = Fibonacci.Fib2();
    Fibonacci f3 = Fibonacci.FibAdd(f1, f2);
    Fibonacci f4 = Fibonacci.FibAdd(f2, f3);
    Fibonacci f5 = Fibonacci.FibAdd(f3, f4);
    Fibonacci f6 = Fibonacci.FibAdd(f4, f5);

    System.out.println(f6.num + " Is a Fibonacci Number");
  }
}
