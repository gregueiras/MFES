predicate isSorted(a: array<int>)
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate isSortedSub(a: array<int>, left: nat, right: nat)
    reads a
    requires 0 <= left <= right < a.Length
{
    forall i, j :: left <= i < j < right ==> a[i] <= a[j]
}


// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>)
  modifies a

  requires a.Length > 0

  ensures isSorted(a)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 0;
    while i < a.Length 
      decreases  a.Length - i
      invariant 0 <= i < a.Length
      invariant multiset(a[..]) == multiset(old(a[..]))
  {
        var j := i;
        while j > 0 && a[j-1] > a[j]
          decreases j
          invariant 0 < j <= i
          invariant isSortedSub(a, j, i + 1)
          invariant multiset(a[..]) == multiset(old(a[..]))
        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
        
        i := i + 1;
    }
}
