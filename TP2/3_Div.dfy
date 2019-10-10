/* 
* Formal specification and verification of a simple method for performing integer division.
* FEUP, MIEIC, MFES, 2019/20.
*/

method abs(n: int) returns (v: int)
  ensures (n >= 0 && n == v) || (n < 0 && n == -v)
 {
  if n < 0 {
    v := -1 * n;
  } else {
    v := n;
  }
}


// Computes the quotient 'q' and remainder 'r' of 
// the integer division of a (non-negative) dividend
// 'n' by a (positive) divisor 'd'.

// if n is positive, r starts with value n
// and needs to be decreased until reaching the desired interval;
method div(n: int, d: int) returns (q: int, r: int)
 requires d > 0
 ensures 0 <= r < d && q * d + r == n
{
  q := 0;
  r := abs(n);

  while r >= d
    decreases  r
    invariant q * d + r == n
  {
    q := q + 1;
    r := r - d;
  }
}

// A simple test case
method Main()
{
    var q, r := div(15, 6);
    assert q == 2;
    assert r == 3;
    print "q = ", q, " r=", r, "\n";

    var a := -5;
    var aB := abs(a);
    assert aB == 5;
    
    a := 5;
    aB := abs(a);
    assert aB == 5;
}