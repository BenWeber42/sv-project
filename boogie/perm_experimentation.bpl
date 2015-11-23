const N: int;
axiom 10 <= N;

var a, old_a, perm: [int]int;

function vi(i: int): bool
{
  0 <= i && i < N
}

function perm(a: [int]int): bool
{
  // WARNING: doesn't work with:
  // (forall i: int :: vi(i) ==> vi(a[i]))
  (forall i: int :: vi(i) ==> 0 <= a[i] && a[i] < N)
  &&
  (forall i, j: int :: 0 <= i && i < j && j < N ==> a[i] != a[j])
}

function perm_of(a, b, perm: [int]int): bool
{
  perm(perm)
  &&
  (forall i: int :: vi(i) ==> a[i] == b[perm[i]])
}

// Returns true iff the elements of 'arr' are small (i.e. values in the range -3N to +3N)
function has_small_elements(arr: [int]int): bool
{
  (forall i: int :: (0 <= i && i < N) ==> (-3 * N <= arr[i] && arr[i] <= 3 * N))
}

function sorted(a: [int]int, lo, up: int): bool
{
  (forall i, j: int :: lo <= i && i <= j && j <= up ==> a[i] <= a[j])
}

procedure init()
  modifies a, perm;
  ensures perm_of(a, old_a, perm);
{
  var k: int;
  k := 0;
  while (k < N)
  {
    a[k] := old_a[k];
    perm[k] := k;
  }
}

procedure swap(i, j: int)
  requires perm_of(a, old_a, perm);
  requires vi(i);
  requires vi(j);
  modifies a, perm;
  ensures a[i] == old(a)[j];
  ensures a[j] == old(a)[i];
  ensures perm_of(a, old_a, perm);
  ensures (forall k: int :: k != i && k != j ==> a[k] == old(a)[k]);
{
  var temp: int;
  
  temp := perm[i];
  perm[i] := perm[j];
  perm[j] := temp; 
  
  temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

// Sorts 'a' using bucket sort or quick sort, as determined by has_small_elements(a)
procedure sort() returns ()
  modifies a, perm;
  ensures perm_of(a, old_a, perm);
  ensures sorted(a, 0, N - 1);
{
  call init();
  if (has_small_elements(a))
  {
    call bucketsort();
  } else
  {
    call quicksort(0, N - 1);
  }
}

procedure quicksort(lo, hi: int)
  requires 0 <= lo;
  requires lo <= hi;
  requires hi < N;
  requires perm_of(a, old_a, perm);
  modifies a, perm;
  ensures perm_of(a, old_a, perm);
  ensures sorted(a, lo, hi);
  ensures (forall k: int :: k < lo ==> a[k] == old(a)[k]);
  ensures (forall k: int :: hi < k ==> a[k] == old(a)[k]);
  ensures (forall k: int :: lo <= k && k <= hi ==> old(a)[lo - 1] <= old(a)[k])
       ==> (forall k: int :: lo <= k && k <= hi ==> a[lo - 1] <= a[k]);
  ensures (forall k: int :: lo <= k && k <= hi ==> old(a)[k] <= old(a)[hi + 1])
       ==> (forall k: int :: lo <= k && k <= hi ==> a[k] <= a[hi + 1]);
{
  var p: int;
   
  if (lo == hi) {
    return;
  } else if (lo + 1 == hi) {
    if (a[lo] > a[hi]) {
      call swap(lo, hi);
    }
    return;
  }
  
  call p := partition(lo, hi - 1, a[hi]);
       
  call swap(p, hi);
  
  if (lo < p) {
    call quicksort(lo, p - 1);
  }
  if (p < hi) {
    call quicksort(p + 1, hi);
  }
}

procedure partition(lo, hi, pivot: int) returns (p: int)
  requires 0 <= lo && lo <= hi && hi < N;
  requires perm_of(a, old_a, perm);
  modifies a, perm;
  ensures perm_of(a, old_a, perm);
  ensures lo <= p && p <= hi + 1;
  ensures (forall k: int :: lo <= k && k < p ==> a[k] < pivot);
  ensures (forall k: int :: p <= k && k <= hi ==> pivot <= a[k]);
  ensures (forall k: int :: k < lo ==> a[k] == old(a)[k]);
  ensures (forall k: int :: hi < k ==> a[k] == old(a)[k]);
  ensures (forall i: int :: i < lo ==> 
    (forall k: int :: lo <= k && k <= hi ==> old(a)[i] <= old(a)[k])
    ==> (forall k: int :: lo <= k && k <= hi ==> a[i] <= a[k])
  );
  ensures (forall i: int :: hi < i ==>
    (forall k: int :: lo <= k && k <= hi ==> old(a)[k] <= old(a)[i])
    ==> (forall k: int :: lo <= k && k <= hi ==> a[k] <= a[i])
  );
{
  var i, j: int;
  
  i := lo;
  j := hi;
  
  while (i < j)
   invariant lo <= i && i <= j && j <= hi;
   invariant perm_of(a, old_a, perm);
   invariant (forall k: int :: lo <= k && k < i ==> a[k] < pivot);
   invariant (forall k: int :: j < k && k <= hi ==> pivot <= a[k]);
   invariant (forall k: int :: i < k && k < j ==> a[k] == old(a)[k]);
   invariant (forall k: int :: k < lo ==> a[k] == old(a)[k]);
   invariant (forall k: int :: hi < k ==> a[k] == old(a)[k]);
   invariant (forall l: int :: l < lo ==> 
    (forall k: int :: lo <= k && k <= hi ==> old(a)[l] <= old(a)[k])
    ==> (forall k: int :: lo <= k && k <= hi ==> a[l] <= a[k])
   );
   invariant (forall l: int :: hi < l ==>
    (forall k: int :: lo <= k && k <= hi ==> old(a)[k] <= old(a)[l])
    ==> (forall k: int :: lo <= k && k <= hi ==> a[k] <= a[l])
   );
  {
    while (a[i] < pivot && i < j)
      invariant lo <= i && i <= j && j <= hi;
      invariant (forall k: int :: lo <= k && k < i ==> a[k] < pivot);
    {
      i := i + 1;
    }
    
    if (i == j) {
      break;
    }
    
    while (pivot <= a[j] && i < j)
      invariant lo <= i && i <= j && j <= hi;
      invariant (forall k: int :: j < k && k <= hi ==> pivot <= a[k]);
    {
      j := j - 1;
    }
    
    if (i == j) {
      break;
    }
    
    call swap(i, j);
  }
  
  if (a[i] < pivot) {
    i := i + 1;
  }
  
  p := i;
}


procedure bucketsort()
  requires perm_of(a, old_a, perm);
  modifies a, perm;
  ensures perm_of(a, old_a, perm);
  ensures sorted(a, 0, N - 1);
{
  

}

