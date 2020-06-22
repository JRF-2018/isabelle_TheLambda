(*
    File:        dTermDef.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

dTermDef = Sum + Nat + Nth + SubOcc + LVariable +

consts
  dTerm     :: i
  dTerm_rec :: [i, i=>i, i=>i, [i, i]=>i, [i, i, i, i]=>i]=>i

  dTag        :: i
  TdVar       :: i=>i
  TdBound     :: i=>i
  TdLam       :: i
  TdApp       :: i

  dArity     :: i=>i
  dTerm_cons  :: [i, i]=>i
  
  dOcc        :: i=>i
  
  dOccinv     :: i=>i
  dSub        :: i=>i
  dsubterm    :: [i, i]=>i
  
datatype <= "univ(LVariable)"
  "dTerm" = dVar ( "x: LVariable" )
          | dBound ( "n: nat" )
          | dLam ( "M: dTerm")
          | dApp ( "M: dTerm", "N: dTerm")
  
defs
  
  dTerm_rec_def
    "dTerm_rec(M, case_var, case_bound, case_fun, case_app) ==   \
\      Vrec(M, %A rec . dTerm_case(case_var, case_bound,  \
\                               %M. case_fun(M, rec`M),   \
\                               %M N. case_app(M, N, rec`M, rec`N),   \
\                               A))"

  dTag_def   "dTag == ((LVariable + nat) + {0}) + {0}"
  TdVar_def  "TdVar(x) == Inl(Inl(Inl(x)))"
  TdBound_def "TdBound(n) == Inl(Inl(Inr(n)))"
  TdLam_def  "TdLam == Inl(Inr(0))"
  TdApp_def  "TdApp == Inr(0)"

  dArity_def 
    "dArity(T) == case(%x. case(%y. case(%z. 0, %z. 0, y),   \
\                               %y. 1, x), %x. 2, T)"

  dTerm_cons_def 
    "dTerm_cons(T, l) == case(%x. case(%y. case(%z. dVar(z),   \ 
\                                               %z. dBound(z), y), \
\                                      %y. dLam(nth(l, 0)), x),   \
\                             %x. dApp(nth(l, 0), nth(l, 1)), T)"
  
  
  dOcc_def  
    "dOcc(M) == dTerm_rec(M,   \
\             %x. Occ_cons(TdVar(x), []),   \
\             %n. Occ_cons(TdBound(n), []),   \
\             %N r. Occ_cons(TdLam, [r]),   \
\             %M N rm rn. Occ_cons(TdApp, [rm, rn]))"

  dOccinv_def
    "dOccinv(x) == THE M. M: dTerm & x = dOcc(M)"

  dSub_def
    "dSub(M) == {<l, dOccinv(Occ_Subtree(l, dOcc(M)))>. <l, T>: dOcc(M)}"

  dsubterm_def
    "dsubterm(M, l) == THE N. <l, N>: dSub(M)"
  
end
