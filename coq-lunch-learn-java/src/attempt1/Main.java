package attempt1;

public class Main {
  public static void main(String[] args){
    Fibonacci f1 = Fibonacci.Fib1();
    Fibonacci f2 = Fibonacci.FibAdd(f1, f1);
    Fibonacci f3 = Fibonacci.FibAdd(f2, f2);

    System.out.println(f3.num + " Is a Fibonacci Number");
  }
}
