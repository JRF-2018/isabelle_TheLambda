(*
    File:        Lambda.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

Lambda = LBeta +

consts
  
  LAQ :: i=>i
  
  Term :: i
  
  Var :: i=>i
  Lam :: [i,i]=>i
  App :: [i,i]=>i

  FV  :: i=>i

  subst :: [i,i,i]=>i

  Beta1 :: [i,i]=>o
  
rules
  
  Infinite_LVariable "Infinite(LVariable)"
  
defs

  LAQ_def "LAQ(M) == {N: LTerm. LAlpha(M, N)}"
  
  Term_def "Term == {LAQ(M). M: LTerm}"
  
  Var_def "Var(x) == {LVar(x)}"
  
  Lam_def 
    "Lam(x, M) == {m': LTerm. M: Term & (EX m: M. LAlpha(m', LLam(x, m)))}"

  App_def
    "App(M, N) == {m: LTerm. M: Term & N: Term &   \
\                            (EX a b. a: M & b: N & m = LApp(a, b))}"

  FV_def
    "FV(M) == INT m: M. LFV(m)"

  subst_def
    "subst(M, x, N) == {m': LTerm. EX m n. m: M & n: N &   \ 
\                         LFreeForIn(n, x, m) &   \
\                         LAlpha(Lsubst(m, x, n), m')}"

  Beta1_def
    "Beta1(M, N) == M: Term & N: Term & (EX m: M. EX n: N. LBeta1(m, n))"
  
end
