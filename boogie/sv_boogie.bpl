const N: int;
// TODO why this? and not 1 <= N?
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

// Returns true iff the elements from a[lo] to a[hi] are sorted
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
/*
  swaps content of a at locations i and j
*/
procedure swap(i, j: int)
  requires perm_of(a, old_a, perm);
  requires vi(i);
  requires vi(j);
  modifies a, perm;
  ensures a[i] == old(a)[j];
  ensures a[j] == old(a)[i];
  ensures perm_of(a, old_a, perm);
  // we do not touch anything other than the values a[j] and a[i]
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

/*
  partitions a between lo and hi into two parts
  one part with all values below the pivot
  another part with all values above the pivot
  Returns: index p which divides a in
           a) elements greater equal pivot
           b) elements smaller pivot
           p is the index of the first element in a
*/
procedure partition(lo, hi, pivot: int) returns (p: int)
  requires 0 <= lo && lo <= hi && hi < N;
  requires perm_of(a, old_a, perm);
  modifies a, perm;
  ensures perm_of(a, old_a, perm);
  ensures lo <= p && p <= hi + 1;
  // all values from lo to p are smaller than the pivot
  ensures (forall k: int :: lo <= k && k < p ==> a[k] < pivot);
  // all values from p to hi are greater-equal the pivot
  ensures (forall k: int :: p <= k && k <= hi ==> pivot <= a[k]);
  // we don't touch the array outside lo and hi
  ensures (forall k: int :: k < lo ==> a[k] == old(a)[k]);
  ensures (forall k: int :: hi < k ==> a[k] == old(a)[k]);
  // all values between lo and hi are greater-equal all values below lo
  ensures (forall i: int :: i < lo ==>
    (forall k: int :: lo <= k && k <= hi ==> old(a)[i] <= old(a)[k])
    ==> (forall k: int :: lo <= k && k <= hi ==> a[i] <= a[k])
  );
  // all values between lo and hi are smaller all values above hi
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

/*
  sorts a from indices lo to hi using quicksort
*/
procedure quicksort(lo, hi: int)
  requires 0 <= lo;
  requires lo <= hi;
  requires hi < N;
  requires perm_of(a, old_a, perm);
  modifies a, perm;
  // a is a permutation of the old a
  ensures perm_of(a, old_a, perm);
  // a from lo to hi is sorted
  ensures sorted(a, lo, hi);
  // we don't modify anything below lo
  ensures (forall k: int :: k < lo ==> a[k] == old(a)[k]);
  // we don't modify anything above hi
  ensures (forall k: int :: hi < k ==> a[k] == old(a)[k]);
  // every element in a between lo and high is larger than a[lo-1] (the largest element before lo)
  ensures (forall k,i: int :: lo <= k && k <= hi ==> old(a)[lo - 1] <= old(a)[k])
       ==> (forall k: int :: lo <= k && k <= hi ==> a[lo - 1] <= a[k]);
  // every element in a between lo and high is smaller than a[hi+1] (the smallest element after hi)
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

/*
  sorts a using bucketsort
*/
procedure bucketsort()
  requires perm_of(a, old_a, perm);
  // TODO: not sure if we need this, but won't hurt
  requires has_small_elements(a);
  modifies a, perm;
  ensures perm_of(a, old_a, perm);
  ensures sorted(a, 0, N - 1);
{
  /*
   * Choose buckets such that each bucket's range is
   * [-3*N, -N), [-N, N) & [N, 3*N] resp.
   *
   * Furthermore choose b1 & b2 such that each bucket's indices is in
   * [0, b1), [b1, b2), [b2, N] resp.
   */
  var b1, b2: int;

  // do first bucket
  call b1 := partition(0, N - 1, -N);

  assert b1 <= N;

  // return with a single quicksort immediately if b1 is
  // outside the range [0,N-1]
  if (b1 == N) {
    call quicksort(0, b1 - 1);
    return;
  }

  if (0 < b1) {
    assert (forall k: int :: 0 <= k && k < b1 ==> a[k] < a[b1]);
    call quicksort(0, b1 - 1);
    // should probably generalize the semantics that establish
    // in partition & quicksort that the respective blocks don't change their
    // relationship to upper and lower limits.
    assert (forall k: int :: 0 <= k && k < b1 ==> a[k] < a[b1]);
  }

  //assert -N <= a[b1];
  //assert (forall k: int :: 0 <= k && k < b1 ==> a[k] < -N);
  assert (forall k: int :: 0 <= k && k < b1 ==> a[k] < a[b1]);

  // do second and third bucket
  call b2 := partition(b1, N - 1, N);

  if (b1 < b2) {
    call quicksort(b1, b2 - 1);
  }
  assert sorted(a, 0, b2 - 1);
  if (b2 < N) {
    call quicksort(b2, N - 1);
  }
  assert sorted(a, 0, N - 1);
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
