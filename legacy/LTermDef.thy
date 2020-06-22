(*
    File:        LTermDef.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

LTermDef = Sum + Nth + OccGraft + LVariable +

consts
  LTerm     :: i
  LTerm_rec :: [i, i=>i, [i, i, i]=>i, [i, i, i, i]=>i]=>i

  LTag        :: i
  TLVar       :: i=>i
  TLLam       :: i=>i
  TLApp       :: i

  LArity     :: i=>i
  LTerm_cons  :: [i, i]=>i
  
  LOcc        :: i=>i
  
  LOccinv     :: i=>i
  LSub        :: i=>i
  Lsubterm    :: [i, i]=>i
  Lgraft  :: [i, i, i]=>i
  
datatype <= "univ(LVariable)"
  "LTerm" = LVar ( "x: LVariable" )
          | LLam ( "x: LVariable", "M: LTerm")
          | LApp ( "M: LTerm", "N: LTerm")
  
defs
  
  LTerm_rec_def
    "LTerm_rec(M, case_var,  case_fun, case_app) ==   \
\      Vrec(M, %A rec . LTerm_case(case_var,   \
\                               %x M . case_fun(x, M, rec`M),   \
\                               %M N . case_app(M, N, rec`M, rec`N),   \
\                               A))"

  LTag_def   "LTag == (LVariable + LVariable) + {0}"
  TLVar_def  "TLVar(x) == Inl(Inl(x))"
  TLLam_def  "TLLam(x) == Inl(Inr(x))"
  TLApp_def  "TLApp == Inr(0)"

  LArity_def 
    "LArity(T) == case(%x. case(%y. 0, %y. 1, x), %x. 2, T)"

  LTerm_cons_def 
    "LTerm_cons(T, l) == case(%x. case(%y. LVar(y),   \
\                                      %y. LLam(y, nth(l, 0)), x),   \
\                             %x. LApp(nth(l, 0), nth(l, 1)), T)"
  
  
  LOcc_def  
    "LOcc(M) == LTerm_rec(M,   \
\             %x. Occ_cons(TLVar(x), []),   \
\             %x N r. Occ_cons(TLLam(x), [r]),   \
\             %M N rm rn. Occ_cons(TLApp, [rm, rn]))"

  LOccinv_def
    "LOccinv(x) == THE M. M: LTerm & x = LOcc(M)"

  LSub_def
    "LSub(M) == {<l, LOccinv(Occ_Subtree(l, LOcc(M)))>. <l, T>: LOcc(M)}"

  Lsubterm_def
    "Lsubterm(M, l) == THE N. <l, N>: LSub(M)"
  
  Lgraft_def
    "Lgraft(x, W, y) == LOccinv(Occ_Graft(LOcc(x), W, LOcc(y)))"

end
