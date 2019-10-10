
/* 
* Formal specification and verification of a dynamic programming algorithm for calculating C(n, k).
* FEUP, MIEIC, MFES, 2019/20.
*/

// Initial recursive definition of C(n, k), based on the Pascal equality.
function method comb(n: nat, k: nat): nat
  requires 0 <= k <= n
  decreases n
  // ensures comb(n, k) == (if k == 0 || k == n then 1 else comb(n-1, k) + comb(n-1, k-1)) // desncessário é o "cálculo" que o dafny faz
{
  if k == 0 || k == n then 1 else comb(n-1, k) + comb(n-1, k-1)  
}

// Calculates C(n, k) iteratively in time O(k*(n-k)) and space O(n-k), with dynamic programming.
// See the slides of the "Algorithm Design and Analysis" for the explanation of the algorithm. 
method combDyn(n: nat, k: nat) returns (res: nat)
  requires 0 <= k <= n
  ensures res == comb(n, k)
{
  var maxj := n - k;
  var c := new nat[1 + maxj];
  forall j | 0 <= j <= maxj 
  {
    c[j] := 1;
  }
  var i := 1;
  while i <= k 
    decreases k - i
    invariant 1 <= i <= k + 1
    invariant forall j :: 0 <= j <= maxj ==> c[j] == comb(j + i - 1, i - 1)
  {
    var j := 1;
    while j <= maxj
      decreases maxj - j
      invariant forall j' :: 0 <= j' <= j ==> c[j'] == comb(j' + i, i)
      invariant forall j' :: j <= j' <= maxj ==> c[j'] == comb(j' + i - 1, i - 1)
    {
      c[j] := c[j] + c[j-1];
      j := j+1;
    } 
    i := i + 1;
  }
  return c[maxj];
}

method Main()
{
  // Statically checked (proved) test cases!    
  assert comb(5, 2) == 10;
  assert comb(5, 0) == 1;
  assert comb(5, 5) == 1;
  
  var r0 := combDyn(5, 5);
  assert r0 == 1;

  // Dynamic checks to see performance differences!
  var res1 := combDyn(35, 10);
  print "combDyn(35, 10) = ", res1, "\n";

  var res2 := comb(35, 10);
  print "comb(35, 10) = ", res2, "\n";
}