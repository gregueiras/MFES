predicate isSorted(a: array<int>)
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}


// Finds a value 'x' in a sorted array 'a', and returns its index,
// or -1 if not found. 
method binarySearch(a: array<int>, x: int) returns (index: int)
  requires isSorted(a)
  //ensures (0 < index < a.Length && a[index] == x) ==> (exists i :: ((0 <= i < a.Length && a[i] == x) ==> index == i))
  ensures index == -1 ==>  forall i :: 0 <= i < a.Length ==> a[i] != x
  ensures index != -1 ==>  0 <= index < a.Length && a[index] == x
{   
    var low, high := 0, a.Length;
    while low < high
      decreases  high - low
      invariant 0 <= low <= high
      invariant low <= high <= a.Length
      invariant forall l :: 0 <= l < low ==> a[l] != x 
      invariant forall r :: high <= r < a.Length ==> a[r] != x 
  {
        var mid := low + (high - low) / 2;
        if 
        {
            case a[mid]  < x => low := mid + 1;
            case a[mid]  > x => high := mid;
            case a[mid] == x => return mid;
        }
    } 
    return -1;
}


method Main() {
  var a := new int[5];
  a[0], a[1], a[2], a[3], a[4] := 1, 4, 6, 8, 9;
  

  var res := binarySearch(a, 8);
  print(res);
  assert res == 3;
  
  var res1 := binarySearch(a, 5);
  print(res1);
  assert res1 == -1;
  
}