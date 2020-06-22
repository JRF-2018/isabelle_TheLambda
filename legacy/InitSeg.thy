(*
    File:        InitSeg.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

InitSeg = Nth + Poset +

consts
  initseg    :: [i,i,i]=>o

defs

  initseg_def	"initseg(A, l, m) == l: list(A) & m: list(A) &   \
\                 (EX x: list(A). l@x = m)"
  
end
