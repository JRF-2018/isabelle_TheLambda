(*
    File:        LAlpha.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

LAlpha = LLambda + Infinite +

consts
  LAV        :: i => i
  LSkeltonEq :: [i, i] => o
  LAlpha :: [i, i]=>o
  
defs
  LAV_def
    "LAV(M) == {x: LVariable. EX l. <l, TLVar(x)>: LOcc(M) |   \
\                    <l, TLLam(x)>: LOcc(M)}"
  
  LSkeltonEq_def
    "LSkeltonEq(M, N) == M: LTerm & N: LTerm &   \
\    (ALL l. (EX x. <l, TLVar(x)>: LOcc(M))   \
\                     <-> (EX x. <l, TLVar(x)>: LOcc(N))) &  \
\    (ALL l. (EX x. <l, TLLam(x)>: LOcc(M))   \ 
\                     <-> (EX x. <l, TLLam(x)>: LOcc(N))) &  \
\    (ALL l. <l, TLApp>: LOcc(M) <-> <l, TLApp>: LOcc(N))"

  LAlpha_def
    "LAlpha(M, N) == LSkeltonEq(M, N) &   \
\    (ALL u. LFreeIn(u, M) <-> LFreeIn(u, N)) &   \
\    (ALL l m. (EX T U. LBoundBy(<l, T>, <m, U>, M))   \
\                      <-> (EX T U. LBoundBy(<l, T>, <m, U>, N)))"

end
