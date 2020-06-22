(*
    File:        FinCont.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

FinCont  =  Finite + Fixedpt +

consts
  finite_set  :: i=>o
  fin_cont     :: [i,i=>i]=>o
  bnd_fin_cont :: [i,i=>i]=>o
  fin_cont_inj_pair :: [i, i=>i, i=>i]=>o
  
defs 
  finite_set_def
    "finite_set(A) == A: Fin(A)"
  
  fin_cont_def
    "fin_cont(D, h) == (ALL X Y. X <= D & Y <= D -->   \ 
\                                      h(X Un Y) = h(X) Un h(Y)) &   \
\                     h(0): Fin(h(D)) & (ALL x:D. h({x}): Fin(h(D)))"
  bnd_fin_cont_def
    "bnd_fin_cont(D, h) == fin_cont(D, h) & h(D) <= D"

  fin_cont_inj_pair_def
    "fin_cont_inj_pair(D, F, G) == (ALL X. X <= D --> X = G(F(x))) &   \
\                                  fin_cont(D, F) & fin_cont(F(D), G)"
  
end
