(*
    File:        OccTools.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

OccTools = ZF_aux + InitSeg + FinBnd + 

consts

  list_dom   :: i=>i
  list_op    :: [i, i] => i

  Occ_fbs_dom :: i=>i
  Occ_fbs_op :: [i, i] => i
  
  Occ_shift   :: [i, i] => i
  Occ_subtree :: [i, i] => i
  Occ_primary :: i=>i
  Occ_cons :: [i, i]=>i
  
  functional :: i=>o
  CorrectArity :: [i, i, i]=>o
  DenseTree :: i=>o

  Occ_range  :: [i, i=>i]=>i

  Occ_cons_cond :: [i, i=>i, i, i=>i] =>o
  Occ_ind_cond :: [i, i=>i, i, i=>i, [i, i]=>i] =>o

defs
  list_op_def
    "list_op(A, X) == {z: univ(A). z = [] | (EX a l. z = Cons(a, l) &   \
\                                                a: A & l: X)}"
  
  list_dom_def
    "list_dom(A) == univ(A)"

  Occ_fbs_dom_def
    "Occ_fbs_dom(Tag) == list_dom(nat) * Tag"

  Occ_fbs_op_def
    "Occ_fbs_op(Tag, X) == list_op(nat, domain(X)) * Tag"
  
  Occ_shift_def
    "Occ_shift(b, X) == {z. y: X, EX l T. z = <Cons(b, l), T> & y = <l, T>}"
  
  Occ_subtree_def
    "Occ_subtree(b, X) == {z. y: X, EX l T. z = <l, T> & y = <Cons(b, l), T>}"

  Occ_primary_def
    "Occ_primary(X) == {z: X. EX T.  z = <[], T>}"

  Occ_cons_def
    "Occ_cons(T, l) == {<[], T>} Un (UN z: length(l). Occ_shift(z, nth(l, z)))"

  functional_def
    "functional(X) == ALL l A B. <l, A>: X & <l, B>: X --> A = B"

  CorrectArity_def
    "CorrectArity(X, T, n) == ALL l. <l, T>: X -->   \
\                           (ALL m. m < n -->  (EX N. <l@[m], N>: X)) &   \
\                           (ALL m. n le m --> ~(EX N. <l@[m], N>: X))"
  
  DenseTree_def
    "DenseTree(X) == (ALL l A m. <l, A>: X & initseg(nat, m, l) -->   \ 
\                                   (EX B. <m, B>: X))"

  Occ_range_def
    "Occ_range(Tag, Arity) ==   \
\            {X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)).   \
\                X ~= 0 & functional(X) & DenseTree(X) &   \
\                (ALL T: Tag. CorrectArity(X, T, Arity(T)))}"

  Occ_cons_cond_def
    "Occ_cons_cond(Terms, Occ, Tag, Arity) ==   \
\      (ALL T: Tag. Arity(T): nat) &   \
\      (ALL T: Tag. ALL l: list(Pow(list(nat)*Tag)). Arity(T) = length(l) &\
\          (ALL z: length(l). EX N: Terms. nth(l, z) = Occ(N))   \
\         --> (EX M: Terms. Occ(M) = Occ_cons(T, l)))"

  Occ_ind_cond_def
    "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons) ==   \
\      (ALL P.   \ 
\        (ALL T: Tag. ALL l: list(Terms).   \
\             Term_cons(T, l): Terms & \
\             Arity(T) = length(l) &   \  
\             Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l)) &   \
\             (ALL z: length(l). nth(l, z): P)  \
\            --> Term_cons(T, l): P \
\         ) --> (ALL M: Terms. M: P))"
  
end
