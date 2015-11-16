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
procedure quicksort(lo: int, hi: int) returns ()
  modifies a;
{
  var p: int;
  if (lo < hi) {
    call p :=  partition(lo, hi);
    call quicksort(lo, p-1);
    call quicksort(p+1, lo);
  }
}
// helper function for quicksort to partition the array
procedure partition(lo:int, hi: int) returns (p: int)
  requires 0 <= lo && hi <= N;
  modifies a;
  ensures lo <= p && hi > p;
  ensures (forall k: int, j: int :: lo <= k && k < p && p <= j && j < hi  ==>  a[k] <= a[j]);
  ensures (forall k: int :: lo <= k && k < p  ==>  a[k] <= old(a)[lo]);
  ensures (forall k: int :: p <= k && k < hi  ==>  old(a)[lo] <= a[k]);
{
  var pivot, i,j,temp: int;
  pivot := a[hi];
  i := lo;
  j := lo;
  while(j <= hi-1) {
    if(a[j] <= pivot) {
      // swap
      call swap(i,j);
      i := i+1;
    }
  }
  call swap(i, hi);
  p := i;
  return;
}

// swap arr[a] with arr[b]
procedure swap(x:int, y:int) returns ()
  requires 0 <= x && y <= N;
  modifies a;
  ensures a[x] == old(a)[y] && a[y] == old(a)[x];
{
  var temp: int;
  temp := a[x];
  a[x] := a[y];
  a[y] := temp;
}

procedure bucketsort(N: int) returns ()
  modifies a;
{
  
}

// Sorts 'a' using bucket sort or quick sort, as determined by has_small_elements(a)
procedure sort() returns ()
  modifies a;
{
  if (has_small_elements(a))
  {
      // sort 'a' using bucket sort
      call bucketsort(N);
  } else
  {
      // sort 'a' using quick sort
      call quicksort(0, N-1);
  }
}
