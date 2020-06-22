(*
    File:        FinBnd.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

FinBnd = MonoInj +

consts
  FinExt	:: [i,i=>i,i]=>i
  fin_bnd       :: [i, i=>i]=>o
  fin_bnd_set   :: [i, i=>i]=>i
  bnd_cont      :: [i, i=>i]=>o

defs

  FinExt_def
    "FinExt(D, h, X) == {0} Un {x: Pow(D). EX z: X. x <= h(z)}"

  fin_bnd_def
    "fin_bnd(x, h) == EX n: nat. x <= nat_rec(n, 0, %n r. h(r))"

  fin_bnd_set_def
    "fin_bnd_set(D, h) == {x: Pow(D). fin_bnd(x, h)}"
  
  bnd_cont_def
    "bnd_cont(D, h) ==   h(D) <= D & \
\                       (ALL X:Pow(Pow(D)). X ~= 0 -->   \
\                                 h(Union(X)) = (UN x: X. h(x)))"

  
end
