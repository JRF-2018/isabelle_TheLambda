(*
    File:        SubOcc.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

SubOcc = OccTools +

consts

  Occ_Subtree :: [i, i] => i

  Term_cons_inj_cond :: [i, i, i=>i, [i,i]=>i]=>o
  
defs
  
  Occ_Subtree_def
    "Occ_Subtree(m, X) == {z. y: X, EX l T. z = <l, T> & y = <m@l, T>}"

  Term_cons_inj_cond_def
    "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)   \
\         == ALL T: Tag. ALL U: Tag. ALL l: list(Terms). ALL m: list(Terms).\
\               Term_cons(T, l): Terms -->   \
\            (Term_cons(T, l) = Term_cons(U, m) <-> T = U &   \
\                  (ALL z: Arity(T). nth(l, z) = nth(m, z)))"
  
end
