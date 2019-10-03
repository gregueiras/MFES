function fib(n : nat ) : nat
  decreases n
  {
    if n < 2 then n else fib(n - 2) + fib(n - 1)
  }

method computeFib (n : nat) returns (x : nat)
ensures fib(n) == x
{
  var i := 0;
  x := 0;
  var y := 1;
  
  while  i < n
    decreases n - i
    invariant x == fib(i)
    invariant y == fib(i + 1)
    invariant i <= n
  {
    x, y := y, x + y; // multiple assignment
    i := i + 1;
  }
}

method Main() {
  print "hello, Dafny\n";
  var x := computeFib(1);
  print x;
  print "\n";

  x := computeFib(2);
  print x;
  print "\n";

  x :=computeFib(3);
  print x;
  print "\n";

  x := computeFib(4);
  print x;
  print "\n";

  x := computeFib(5);
  print x;
  print "\n";
  
}