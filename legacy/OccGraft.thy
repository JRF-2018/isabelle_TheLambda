(*
    File:        OccGraft.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

OccGraft = SubOcc +

consts

  lists_subtree :: [i, i] => i
  
  Occ_Shift   :: [i, i] => i
  
  Incomparable :: i=>o

  Occ_Graft1 :: [i, i, i] => i

  Occ_Graft  :: [i, i, i] => i
  
defs

  lists_subtree_def
    "lists_subtree(b, W) == {z. y: W, y = Cons(b, z)}"

  Occ_Shift_def
    "Occ_Shift(m, X) == {z. y: X, EX l T. z = <m@l, T> & y = <l, T>}"

  Incomparable_def
    "Incomparable(W) == ALL l: W. ALL m: W. \
\              initseg(nat, l, m) | initseg(nat, m, l) --> l = m"

  Occ_Graft1_def
    "Occ_Graft1(X, l, Y) == (X - {u: X. EX m T. u = <m, T> &   \
\                                          initseg(nat, l, m)}) Un   \
\                            Occ_Shift(l, Y)"
  
  Occ_Graft_def
    "Occ_Graft(X, W, Y)  == (X - (UN l: W. {u: X. EX m T. u = <m, T> &   \
\                                                   initseg(nat, l, m)})) \ 
\                          Un (UN l: W. Occ_Shift(l, Y))"

end
