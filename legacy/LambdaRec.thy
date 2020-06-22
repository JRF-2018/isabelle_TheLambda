(*
    File:        LambdaRec.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

LambdaRec = Lambda +

consts

defs

  DestrVar_def
    "DestrVar(M) == Union({x: LVariable. LVar(x): M})";

  DestrLam1_def
    "DestrLam1(M) == Union({x: LVariable. EX m. LLam(x, m): M})";

  DestrLam2_def
    "DestrLam(x, M) == {m: LTerm. LLam(x, m): M}"

  DestrApp1_def
    "DestrApp1(M) == {m: LTerm. EX n. LApp(m, n): M}"
  
  DestrApp2_def
    "DestrApp2(M) == {n: LTerm. EX m. LApp(m, n): M}"

