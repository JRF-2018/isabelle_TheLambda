(*
    File:        dB.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

dB = dAlpha + LAlpha +

consts
  
  dB :: i=>i

  LAlpha3 :: [i,i] => o

  dsubst :: [i, i, i]=>i
  isSubst1 :: [i,i,i,i]=>o
  isSubst2 :: [i,i,i,i]=>o

defs

  dB_def
    "dB(M) == LTerm_rec(M, %x. dVar(x), %x M r. dLam(dAbst(r, x, 0)),   \
\                          %M N rm rn. dApp(rm, rn))"

  LAlpha3_def
    "LAlpha3(M, N) == M: LTerm & N: LTerm & dB(M) = dB(N)"

  dsubst_def
    "dsubst(M, x, N) == dSubst(dAbst(M, x, 0), 0, N)"
  
  isSubst1_def
    "isSubst1(A, x, B, C) == EX A'. LAlpha(A, A') & LFreeForIn(B, x, A') &   \
\       LAlpha(Lsubst(A', x, B), C)"

  isSubst2_def
    "isSubst2(A, x, B, C) == A: LTerm & B: LTerm & C: LTerm & x: LVariable &  \
\       dsubst(dB(A), x, dB(B)) = dB(C)"

end
