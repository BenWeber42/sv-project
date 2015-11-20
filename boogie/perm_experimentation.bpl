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
{
  var temp: int;
  
  temp := perm[i];
  perm[i] := perm[j];
  perm[j] := temp; 
  
  temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}

procedure sort()
  modifies a, perm;
  ensures perm_of(a, old_a, perm);
{
  call init();
  call swap(3, 4);
  call swap(5, 6);
  call swap(7, 1);
  call swap(3, 6);
  call swap(1, 4);
}

