method noRepetitionsQuadratic(arr : array<nat>) returns (b: bool)
ensures b == true ==> forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j]
ensures b == false ==> exists i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j && arr[i] == arr[j]
{
    var i := 0;
    b := true;

    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant b ==> forall k, l :: 0 <= k < i && 0 <= l < i && k != l ==> arr[k] != arr[l]
    {
        var v := arr[i];
        var j := 0;

        while j < arr.Length
            invariant 0 <= j <= arr.Length
            invariant b ==> forall k :: 0 <= k < j && k != i ==> arr[k] != arr[i]
        {
            var u := arr[j];
            if (j != i && u == v) {
                b := false;
                return;
            }
            j := j + 1;
        }
        i := i + 1;
    }
}


method noRepetitionsLinear(arr: array<nat>) returns (b: bool)
  ensures arr.Length == 0 ==> b == true
  ensures b == true ==> forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j ==> arr[i] != arr[j]
  ensures forall i, j :: 0 <= i < arr.Length && 0 <= j < arr.Length && i != j && arr[i] == arr[j] ==> b == false
  
  
{
  if arr.Length == 0 {
    return true;
  }

  var maxValue := arr[0];
  var idx1 := 0;
  while idx1 < arr.Length
    invariant 0 <= idx1 <= arr.Length 
    invariant maxValue >= arr[0]
    invariant forall k :: 0 <= k < idx1 ==> arr[k] <= maxValue 
  {
    if arr[idx1] > maxValue {
      maxValue := arr[idx1];
    }
    idx1 := idx1 + 1;
  }

 
  var seen: array<bool> := new bool[maxValue + 1];

  
  var idx := 0;
  while idx < arr.Length
    invariant 0 <= idx <= arr.Length
    invariant forall i, j :: 0 <= i < j < idx ==> arr[i] != arr[j]
    invariant forall i :: 0 <= i < idx ==> arr[i] < seen.Length && seen[arr[i]] == true 
  

  {
    var value := arr[idx];

    if seen[value] == false {
      seen[value] := true; 
    } else {
      return false; 
    }

    idx := idx + 1;
  }

  return true; 
}
