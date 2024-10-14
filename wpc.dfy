method Abs(x : int) returns (y : int) 
  ensures 0 <= y
  ensures 0 <= x ==> y == x
  ensures x < 0 ==> y == -x
{
  if (x < 0)
   {y := -x;}
  else
   {y := x;}
}


method Q2(x : int, y : int) returns (big : int, small : int) 
  requires x != y
  ensures big > small
{
  if (x > y)
   {big, small := x, y;}
  else
   {big, small := y, x;}
}


method Q3(n0 : int, m0 : int) returns (res : int)
    ensures res == n0*m0
{
  var n, m : int;
  res := 0;
  if (n0 >= 0)
       {n,m := n0, m0;}
  else 
       {n,m := -n0, -m0;}
  while (0 < n) 
    invariant res + n*m == n0*m0
    decreases n
  {
    res := res + m;
    n := n - 1;
  }
}

function fact(n : int) : (res : int)
  requires n > 0
  ensures (n==1) == (res==1)
  decreases n
  {
    if n == 1 then 1 else n * fact(n-1)
  }

method ComputeFact(n : nat) returns (res : nat)
  requires n > 0
  ensures 
    && (res == fact(n)) // spec matches
  {
    res := 1;
    var i := 2;
    while (i <= n)
      invariant
        && (2<=i<=n+1) // bound range of i
        && (res == fact(i-1)) // equivalent to spec
      decreases n-i
    {
      res := res * i;
      i := i + 1;
    }
  }



method main()
{
    var result := Q3(2,3);
    assert result == 6;
}

