const N: int;
axiom 0 <= N;

const old_a: [int]int;
var a, perm: [int]int;

function vi(i: int): bool
{
  0 <= i && i < N
}

function perm(a: [int]int): bool
{
  (forall i: int :: vi(i) ==> vi(a[i]))
  &&
  (forall i, j: int :: vi(i) && vi(j) && i != j ==> a[i] != a[j])
}

function perm_of(a, b, perm: [int]int): bool
{
  perm(perm)
  &&
  (forall i: int :: vi(i) ==> a[perm[i]] == b[i])
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
  requires vi(i) && vi(j);
  modifies a, perm;
  //ensures a[i] == old(a)[j];
  //ensures a[j] == old(a)[i];
  //ensures perm_of(a, old_a, perm);
{
  var temp: int;
  
  temp := perm[i];
  perm[i] := perm[j];
  perm[j] := temp; 
  
  assert perm[i] == old(perm)[j];
  assert perm[j] == old(perm)[i];
  
  assert (forall k: int :: vi(k) && k != i && k != j ==> perm[k] == old(perm)[k]);
  
  assert (forall k: int :: vi(k) ==> vi(perm[k]));
  
  //temp := a[i];
  //a[i] := a[j];
  //a[j] := temp;
}

procedure sort()
  modifies a, perm;
{
  call init();
}
