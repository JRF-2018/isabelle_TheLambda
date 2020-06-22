(*
    File:        Poset.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

Poset = ZF + FinCard +

consts
  poset :: [[i,i]=>o, i]=>o
  chain :: [[i,i]=>o, i]=>o

  invrel :: [[i, i]=>o, i, i]=> o
  
  least :: [[i,i]=>o, i, i]=>o
  greatest :: [[i, i]=>o, i, i]=>o

  minimal :: [[i, i]=>o, i, i]=>o
  maximal :: [[i, i]=>o, i, i]=>o
  
  downset :: [[i, i]=>o, i, i]=>i
  upset :: [[i, i]=>o, i, i]=>i

  upperbound :: [[i, i]=>o, i, i]=>i
  lowerbound :: [[i, i]=>o, i, i]=>i

defs
  
  poset_def 
    "poset(R, P) == (ALL x: P. R(x, x)) &   \
\            (ALL x: P. ALL y: P. R(x, y) & R(y, x) --> x = y) &   \
\            (ALL x: P. ALL y: P. ALL z: P. R(x, y) & R(y, z) --> R(x, z))"
  
  chain_def
     "chain(R, P) == poset(R, P) & (ALL x: P. ALL y: P. R(x, y) | R(y, x))"

  invrel_def
    "invrel(R, x, y) == R(y, x)"
  
  least_def
     "least(R, P, x) == x: P & (ALL y: P. R(x, y))"

  greatest_def
     "greatest(R, P, x) == x: P & (ALL y: P. R(y, x))"

  minimal_def
     "minimal(R, P, x) == x: P & (ALL y: P. R(y, x) --> y = x)"
  
  maximal_def
     "maximal(R, P, x) == x: P & (ALL y: P. R(x, y) --> y = x)"

  downset_def
     "downset(R, P, x) == {y: P. R(y, x)}"
  
  upset_def
      "upset(R, P, x) == {y: P. R(x, y)}"
  
  upperbound_def
      "upperbound(R, P, S) == {x: P. ALL y: S. R(y, x)}"

  lowerbound_def
      "lowerbound(R, P, S) == {x: P. ALL y: S. R(x, y)}"

end
