(*
    File:        SndLAlpha.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

SndLAlpha = LAlpha +

consts
  LAlpha2 :: i
  
inductive
  domains "LAlpha2" <= "LTerm * LTerm"
  intrs
    LVarI "x: LVariable ==> <LVar(x), LVar(x)>: LAlpha2"
    LAppI "[| <A, C>: LAlpha2; <B, D>: LAlpha2 |]   \
\               ==> <LApp(A, B), LApp(C, D)>: LAlpha2"
    LLamI "[| x: LVariable; y: LVariable; <M, N>: LAlpha2;   \ 
\             y ~: LFV(N) - {x}; LFreeForIn(LVar(y), x, N) |]  \ 
\           ==> <LLam(x, M), LLam(y, Lsubst(N, x, LVar(y)))>: LAlpha2"

    transI "[| <A, B>: LAlpha2; <B, C>: LAlpha2 |] ==> <A, C>: LAlpha2"

  type_intrs "LTerm.intrs @ [SigmaI, Lsubst_type]"
  type_elims "[SigmaE2]"
  
end
