(*
    File:        LLambda.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

LLambda = LTermDef + Poset +

consts
  LBinding :: [i, i, i] => o
  LBoundBy :: [i, i, i] => o

  LBoundIn :: [i, i] => o
  LFreeIn :: [i, i] => o

  LFV :: i => i
  LFO :: [i, i] => i
  
  Lsubst :: [i, i, i] => i

  LFreeForIn :: [i, i, i]=>o
  
defs
  LBinding_def
    "LBinding(v, u, M) == M: LTerm & u: LOcc(M) & v: LOcc(M) &   \
\        (EX x l m. u = <l, TLVar(x)> & v = <m, TLLam(x)> &   \
\                    initseg(nat, m, l))"
  
  LBoundBy_def
    "LBoundBy(u, v, M) == EX x l m. u = <m, TLVar(x)> & v = <l, TLLam(x)> &   \
\       greatest(initseg(nat), {n:list(nat). EX T. LBinding(<n, T>, u, M)}, l)"
  
  LBoundIn_def
    "LBoundIn(u, M) == M: LTerm & u: LOcc(M) & (EX l x. u = <l, TLVar(x)> &   \
\         (EX v: LOcc(M). (EX m. v = <m, TLLam(x)> & initseg(nat, m, l))))"
  
  LFreeIn_def
    "LFreeIn(u, M) == M: LTerm & u: LOcc(M) & (EX l x. u = <l, TLVar(x)> & \
\        ~(EX v: LOcc(M). (EX m. v = <m, TLLam(x)> & initseg(nat, m, l))))"
  
  LFV_def
    "LFV(M) == {x: LVariable. EX l.  LFreeIn(<l, TLVar(x)> , M)}"
  
  LFO_def
    "LFO(x, M) == {u: list(nat)*LTag. EX l. u = <l, TLVar(x)> & LFreeIn(u, M)}"

  Lsubst_def
    "Lsubst(M, x, N) == Lgraft(M, domain(LFO(x, M)), N)"

  LFreeForIn_def
    "LFreeForIn(N, x, M) == N: LTerm & x: LVariable & M: LTerm & \
\      (ALL z: LFV(N). ~ (EX l m.   \
\         LFreeIn(<l, TLVar(x)>, M) &   \
\         <m, TLLam(z)>: LOcc(M) & initseg(nat, m, l)))"
  
end
