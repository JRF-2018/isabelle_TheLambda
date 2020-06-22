(*
    File:        NBQuant.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

NBQuant  =  Nat +

consts
  NBall :: [i, i=>o]=>o
  NBex  :: [i, i=>o]=>o
  
syntax

  "@NBall"     :: [pttrn, i, o] => o        ("(3ALL _<_:nat./ _)" 10)
  "@NBex"      :: [pttrn, i, o] => o        ("(3EX _<_:nat./ _)" 10)

  
translations
  "ALL x<A:nat. P"  == "NBall(A, %x. P)"
  "EX x<A:nat. P"   == "NBex(A, %x. P)"

defs

  NBall_def      "NBall(A, P) == A: nat & (ALL x. x<A --> P(x))"
  NBex_def       "NBex(A, P) == A: nat & (EX x. x<A & P(x))"
  
end
