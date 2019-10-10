/* 
* Formal verification of the bubble sort algorithm with Dafny.
* FEUP, MIEIC, MFES, 2019/20.
*/

type T = int // for demo purposes, but could be other type

// Checks if array 'a' is sorted.
predicate isSorted(a: array<T>)
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// Sorts array 'a' using the bubble sort algorithm.
method bubbleSort(a: array<T>)
  modifies a
  ensures isSorted(a)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var i := a.Length; // len of left subarray to sort
  while i > 1
    decreases  i - 1
    invariant forall l, r :: 0 <= l < r < a.Length && r >= i ==> a[l] <= a[r] // o lado esquerdo está ordenado e os números da direita são maiores que pos da esquerda
    invariant 0 <= i <= a.Length // como alteramos o i, é boa prática dar a gama de valores que i pode tomar
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := 0; // used to scan left subarray
    while j < i - 1
      decreases  i - 1 - j
        invariant forall l, r :: 0 <= l < r < a.Length && (r >= i || r == j) ==> a[l] <= a[r] // o j é maior ou igual a todos os elementos à esquerda
        invariant 0 <= j < i // como alteramos o j, é boa prática dar a gama de valores que i pode tomar
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        if (a[j] > a[j+1]) 
        { 
          a[j], a[j+1] := a[j+1], a[j]; 
        }
        j := j+1; 
    }
    i := i-1;
  }
}


method printArray<T>(a: array<T>)
{
      var i := 0;
      print "{";
      while (i < a.Length)
      decreases a.Length - i;
      {
          if (i > 0)
          {
              print ", ";
          }
          print a[i];
          i := i+1;
      }
      print "}\n" ;
}


 method Main() {
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 9, 4, 6, 3, 8;
    print "before sorting: ";
    printArray(a);  
    bubbleSort(a);
    print "after sorting: ";
    printArray(a);  
}