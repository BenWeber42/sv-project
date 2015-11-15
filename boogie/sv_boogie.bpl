// Introduce a constant 'N' and postulate that it is non-negative
const N: int;
axiom 0 <= N;

// Declare a map from integers to integers.
// 'a' should be treated as an array of 'N' elements, indexed from 0 to N-1
var a: [int]int;

// Returns true iff the elements of 'arr' are small (i.e. values in the range -3N to +3N)
function has_small_elements(arr: [int]int): bool
{
  (forall i: int :: (0 <= i && i < N) ==> (-3 * N <= arr[i] && arr[i] <= 3 * N))
}

// Recursive implementation of quicksort
procedure quicksort(arr: [int]int, lo: int, hi: int) returns (new_arr: [int]int) {
  var p: int;
  if (lo < hi) {
    call p :=  partition(arr, lo, hi);
    call new_arr := quicksort(arr, lo, p-1);
    call new_arr := quicksort(new_arr, p+1, lo);
  }
}
// helper function for quicksort to partition the array
procedure partition(arr: [int]int, lo:int, hi: int) returns (k: int) {
  var pivot, i,j,temp: int;
  pivot := arr[hi];
  i := lo;
  j := lo;
  while(j <= hi-1) {
    if(arr[j] <= pivot) {
      // swap
      call arr := swap(arr, i,j);
      i := i+1;
    }
  }
  call arr := swap(arr, i, hi);
  k := i;
  return;
}

// swap arr[a] with arr[b]
procedure swap(arr: [int]int, a:int, b:int) returns (new_arr: [int]int) {
  var temp: int;
  new_arr := arr;
  temp := new_arr[a];
  new_arr[a] := new_arr[b];
  new_arr[b] := temp;
}

// Sorts 'a' using bucket sort or quick sort, as determined by has_small_elements(a)
procedure sort() returns ()
  modifies a;
{
  if (has_small_elements(a))
  {
      // sort 'a' using bucket sort
      // TODO: replace with bucket sort later
      call a := quicksort(a, 0, N-1);
  } else
  {
      // sort 'a' using quick sort
      call a := quicksort(a, 0, N-1);
  }
}

