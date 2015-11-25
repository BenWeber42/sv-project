const N: int;
axiom 0 <= N;

var a, old_a, perm: [int]int;

/*
  Whether i is a valid index (i.e. i is in [0, N)).
*/
function vi(i: int): bool
{
  0 <= i && i < N
}

/*
  Whether a is a permutation array.
  I.e. all elements are distinct and in the range [0, N)
*/
function perm(a: [int]int): bool
{
  // WARNING: doesn't work with (timeout):
  // (forall i: int :: vi(i) ==> vi(a[i]))
  (forall i: int :: vi(i) ==> 0 <= a[i] && a[i] < N)
  &&
  (forall i, j: int :: 0 <= i && i < j && j < N ==> a[i] != a[j])
}

/*
  Returns true iff perm describes a valid permutation
  of a and b
*/
function perm_of(a, b, perm: [int]int): bool
{
  perm(perm)
  &&
  (forall i: int :: vi(i) ==> a[i] == b[perm[i]])
}

/*
  Returns true iff the elements of 'arr' are small
  (i.e. all values in the range [-3N, +3N])
*/
function has_small_elements(arr: [int]int): bool
{
  (forall i: int :: (0 <= i && i < N) ==> (-3 * N <= arr[i] && arr[i] <= 3 * N))
}

/*
  Returns true iff the elements from a[lo] to a[hi] are sorted
  Note: An array of length 1 or less is conservatively assumed not to be sorted.
*/
function sorted(a: [int]int, lo, hi: int): bool
{
  hi - lo >= 1
  &&
  (forall i, j: int :: lo <= i && i <= j && j <= hi ==> a[i] <= a[j])
}

/*
  swaps content of a at locations i and j
*/
procedure swap(i, j: int)
  requires vi(i);
  requires vi(j);
  modifies a, perm;
  ensures a[i] == old(a)[j];
  ensures a[j] == old(a)[i];
  // preserves the permutation property
  ensures perm_of(old(a), old(old_a), old(perm)) ==> perm_of(a, old_a, perm);
  // we do not touch anything other than the values a[j] and a[i]
  ensures (forall k: int :: k != i && k != j ==> a[k] == old(a)[k]);
{
  var temp: int;

  if (perm_of(old(a), old(old_a), old(perm))) {
    temp := perm[i];
    perm[i] := perm[j];
    perm[j] := temp;
  }

  temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

/*
  partitions a between lo and hi into two parts:
           (a) elements greater equal pivot
           (b) elements smaller pivot
  Returns: p, the index of the first element in (a)
*/
procedure partition(lo, hi, pivot: int) returns (p: int)
  requires 0 <= lo && lo <= hi && hi < N;
  modifies a, perm;
  // preserves the permutation property
  ensures perm_of(old(a), old(old_a), old(perm)) ==> perm_of(a, old_a, perm);
  // valid partition index
  ensures lo <= p && p <= hi + 1;
  // all values from lo to p are smaller than the pivot
  ensures (forall k: int :: lo <= k && k < p ==> a[k] < pivot);
  // all values from p to hi are greater-equal the pivot
  ensures (forall k: int :: p <= k && k <= hi ==> pivot <= a[k]);
  // we don't touch the array outside lo and hi
  ensures (forall k: int :: k < lo ==> a[k] == old(a)[k]);
  ensures (forall k: int :: hi < k ==> a[k] == old(a)[k]);
  // if some values below lo were smaller-equal than all values between lo and hi,
  // then those values will still be smaller-equal than all values between lo and hi afterwards.
  // (implied by the permutation property and that values outside lo and hi
  // aren't changed, but boogie can better make use of it, if it's stated
  // explicitely)
  ensures (forall i: int :: i < lo ==>
    (forall k: int :: lo <= k && k <= hi ==> old(a)[i] <= old(a)[k])
    ==> (forall k: int :: lo <= k && k <= hi ==> a[i] <= a[k])
  );
  // if some values above hi were bigger-equal than all values between lo and hi,
  // then those values will still be bigger-euqal than all values between lo and hi afterwards.
  // (implied by the permutation property and that values outside lo and hi
  // aren't changed, but boogie can better make use of it, if it's stated
  // explicitely)
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
   invariant perm_of(old(a), old(old_a), old(perm)) ==> perm_of(a, old_a, perm);
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
    // find first candidate to be swapped
    while (a[i] < pivot && i < j)
      invariant lo <= i && i <= j && j <= hi;
      invariant (forall k: int :: lo <= k && k < i ==> a[k] < pivot);
    {
      i := i + 1;
    }

    // finished
    if (i == j) {
      break;
    }

    // find second candidate to be swapped
    while (pivot <= a[j] && i < j)
      invariant lo <= i && i <= j && j <= hi;
      invariant (forall k: int :: j < k && k <= hi ==> pivot <= a[k]);
    {
      j := j - 1;
    }

    // finished
    if (i == j) {
      break;
    }

    call swap(i, j);
  }

  // take care of special case
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
  modifies a, perm;
  // preserves the permutation property
  ensures perm_of(old(a), old(old_a), old(perm)) ==> perm_of(a, old_a, perm);
  // a from lo to hi is sorted if it makes sense
  ensures hi - lo >= 1 ==> sorted(a, lo, hi);
  // leaves a and perm untouched otherwise
  ensures hi - lo < 1 ==> (forall i: int :: vi(i) ==> a[i] == old(a)[i]);
  ensures hi - lo < 1 ==> (forall i: int :: vi(i) ==> perm[i] == old(perm)[i]);
  // we don't modify anything below lo
  ensures (forall k: int :: k < lo ==> a[k] == old(a)[k]);
  // we don't modify anything above hi
  ensures (forall k: int :: hi < k ==> a[k] == old(a)[k]);
  // if some values below lo were smaller-equal than all values between lo and hi,
  // then those values will still be smaller-equal than all values between lo and hi afterwards.
  // (implied by the permutation property and that values outside lo and hi
  // aren't changed, but boogie can better make use of it, if it's stated
  // explicitely)
  ensures (forall i: int :: i < lo ==>
   (forall k: int :: lo <= k && k <= hi ==> old(a)[i] <= old(a)[k])
   ==> (forall k: int :: lo <= k && k <= hi ==> a[i] <= a[k])
  );
  // if some values above hi were bigger-equal than all values between lo and hi,
  // then those values will still be bigger-euqal than all values between lo and hi afterwards.
  // (implied by the permutation property and that values outside lo and hi
  // aren't changed, but boogie can better make use of it, if it's stated
  // explicitely)
  ensures (forall i: int :: hi < i ==>
   (forall k: int :: lo <= k && k <= hi ==> old(a)[k] <= old(a)[i])
   ==> (forall k: int :: lo <= k && k <= hi ==> a[k] <= a[i])
  );
{
  var p: int;

  // take care of base cases
  if (lo == hi) {
    return;
  } else if (lo + 1 == hi) {
    if (a[lo] > a[hi]) {
      call swap(lo, hi);
    }
    return;
  }

  // recursive case: partition, then quicksort each partition if necessary
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
  modifies a, perm;
  // preserves the permutation property
  ensures perm_of(old(a), old(old_a), old(perm)) ==> perm_of(a, old_a, perm);
  // sorts all of a if it makes sense
  ensures N >= 2 ==> sorted(a, 0, N - 1);
  // leaves a and perm untouched otherwise
  ensures N < 2 ==> (forall i: int :: vi(i) ==> a[i] == old(a)[i]);
  ensures N < 2 ==> (forall i: int :: vi(i) ==> perm[i] == old(perm)[i]);
{
  /*
   * Choose buckets such that each bucket's range is
   * [-3*N, -N), [-N, N) & [N, 3*N] resp.
   *
   * Furthermore choose b1 & b2 such that each bucket's indices is in
   * [0, b1), [b1, b2), [b2, N] resp.
   */
  var b1, b2: int;

  // if N <= 1 the sortedness property doesn't make any sense
  if (N <= 1) {
    return;
  }
  
  // do first bucket
  call b1 := partition(0, N - 1, -N);

  // sort the first bucket only if it contains elements
  if (0 < b1) {
    call quicksort(0, b1 - 1);
  }

  // if all elements were in the first bucket, we're done
  if (b1 == N) {
    return;
  }
  
  // do second and third bucket
  call b2 := partition(b1, N - 1, N);

  // sort second bucket only if it contains elements
  if (b1 < b2) {
    call quicksort(b1, b2 - 1);
  }
  // sort third bucket only if it contains elements
  if (b2 < N) {
    call quicksort(b2, N - 1);
  }
}

/*
  Sorts 'a' using bucket sort or quick sort
  as determined by has_small_elements(a)
*/
procedure sort() returns ()
  modifies a, perm;
  // preserves the permutation property
  ensures perm_of(old(a), old(old_a), old(perm)) ==> perm_of(a, old_a, perm);
  // sorts all of a if it makes sense
  ensures N >= 2 ==> sorted(a, 0, N - 1);
  // leaves a and perm untouched otherwise
  ensures N < 2 ==> (forall i: int :: vi(i) ==> a[i] == old(a)[i]);
  ensures N < 2 ==> (forall i: int :: vi(i) ==> perm[i] == old(perm)[i]);
{
  if (has_small_elements(a))
  {
    call bucketsort();
  } else
  {
    call quicksort(0, N - 1);
  }
}
