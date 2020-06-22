(*
    File:        dAlpha.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

dAlpha = dLambda + 

consts
  dSkeltonEq :: [i, i] => o
  dAlpha :: [i, i]=>o
  
defs
  
  dSkeltonEq_def
    "dSkeltonEq(M, N) == M: dTerm & N: dTerm &   \
\    (ALL l. (EX x. <l, TdVar(x)>: dOcc(M))   \
\                     <-> (EX x. <l, TdVar(x)>: dOcc(N))) &  \
\    (ALL l. (EX n. <l, TdBound(n)>: dOcc(M))   \
\                     <-> (EX n. <l, TdBound(n)>: dOcc(N))) &  \
\    (ALL l. <l, TdLam>: dOcc(M) <-> <l, TdLam>: dOcc(N)) & \
\    (ALL l. <l, TdApp>: dOcc(M) <-> <l, TdApp>: dOcc(N))"

  dAlpha_def
    "dAlpha(M, N) == dSkeltonEq(M, N) &   \
\    (ALL l x. <l, TdVar(x)>: dOcc(M) <-> <l, TdVar(x)>: dOcc(N)) & \
\    (ALL l m. (EX T U. dBoundBy(<l, T>, <m, U>, M))   \
\                      <-> (EX T U. dBoundBy(<l, T>, <m, U>, N)))"

end
