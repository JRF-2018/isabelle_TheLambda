(*
    File:        FinBndEx.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

FinBndEx = FinBnd +

consts
  h_nat         :: i=>i
  h_tn          :: i=>i

defs
  h_nat_def  "h_nat(X) == {0} Un {succ(x). x: X}"
  h_tn_def   "h_tn(X) == if(nat: X | X = nat, succ(nat), h_nat(X))"
  
end
