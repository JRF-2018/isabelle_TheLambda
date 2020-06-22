(*
    File:        LBeta.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

LBeta = LAlpha +

consts

  LBeta1  :: [i, i]=>o

  LBV     :: i=>i
  
defs

  LBeta1_def
    "LBeta1(M, N) == M: LTerm & \
\       (EX u: LSub(M). EX l x A B. u = <l, LApp(LLam(x, A), B)> & \
\           LFreeForIn(B, x, A) & \
\           N = LOccinv(Occ_Graft1(LOcc(M), l, LOcc(Lsubst(A, x, B)))))"

  LBV_def
    "LBV(M) == {x: LVariable. EX l. <l, TLLam(x)>: LOcc(M)}"
  
end
