// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>)
{
    var i := 0;
    while i < a.Length 
    {
        var j := i;
        while j > 0 && a[j-1] > a[j]
        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
        i := i + 1;
    }
}
