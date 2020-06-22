(*
    File:        Length.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

Length = Lambda + dLambda +

consts
  LLength    :: i=>i
  
  Length    :: i=>i

defs

  LLength_def
    "LLength(M) == LTerm_rec(M, %x. 0, %x m r. succ(r),   \ 
\                               %m n rm rn. succ(rm Un rn))"

  Length_def
    "Length(M) == THE n. n: (INT m: M. {LLength(m)})"
  
end
