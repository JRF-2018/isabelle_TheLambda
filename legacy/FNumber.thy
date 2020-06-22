(*
    File:        FNumber.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
 
    An example theory about Occ.
*)

FNumber = Sum + Nth + OccGraft +

consts
  FNum     :: i
  FNum_rec :: [i, i, [i, i]=>i]=>i

  FTag        :: i
  TFZero      :: i
  TFSucc      :: i

  FArity     :: i=>i
  FTerm_cons  :: [i, i]=>i
  
  FOcc        :: i=>i
  
  FOccinv     :: i=>i
  FSub        :: i=>i
  Fsubterm    :: [i, i]=>i
  Fgraft  :: [i, i, i]=>i

  FZO         :: i=>i
  Fadd      :: [i, i]=>i
  Faddr       :: i=>i
  Fdiff        :: [i, i]=>i
  
datatype <= "univ(0)"
  "FNum" = FZero | FSucc("n: FNum")
  
defs
  
  FNum_rec_def
    "FNum_rec(M, case_Zero, case_Succ) ==   \
\      Vrec(M, %A rec . FNum_case(case_Zero,   \
\                               %M. case_Succ(M, rec`M),   \
\                               A))"

  FTag_def   "FTag == {0} + {0}"
  TFZero_def  "TFZero == Inl(0)"
  TFSucc_def  "TFSucc == Inr(0)"


  FArity_def 
    "FArity(T) == case(%y. 0, %y. 1, T)"

  FTerm_cons_def 
    "FTerm_cons(T, l) == case(%x. FZero, %x. FSucc(nth(l, 0)), T)"
  
  FOcc_def  
    "FOcc(M) == FNum_rec(M, Occ_cons(TFZero, []),   \
\             %M r. Occ_cons(TFSucc, [r]))"

  FOccinv_def
    "FOccinv(x) == THE M. M: FNum & x = FOcc(M)"

  FSub_def
    "FSub(M) == {<l, FOccinv(Occ_Subtree(l, FOcc(M)))>. <l, T>: FOcc(M)}"

  Fsubterm_def
    "Fsubterm(M, l) == THE N. <l, N>: FSub(M)"
  
  Fgraft_def
    "Fgraft(x, W, y) == FOccinv(Occ_Graft(FOcc(x), W, FOcc(y)))"

  FZO_def
     "FZO(M) == {u: FOcc(M). EX l. u = <l, TFZero>}"

  Fadd_def
    "Fadd(M, N) == Fgraft(M, domain(FZO(M)), N)"
  
  Faddr_def  
    "Faddr(M) == FNum_rec(M, [], %M r. Cons(0, r))"

  Fdiff_def
    "Fdiff(M, N) == Fsubterm(M, Faddr(N))"
  
end
