(*
    File:        Nth.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

Nth  =  ZF_aux + List +

consts
  nth :: [i,i]=>i
  mapnth :: [[i, i]=>i, i]=>i

defs

  nth_def        "nth(l, i) == hd(drop(i, l))"
  mapnth_def
    "mapnth(f, l) == rec(length(l), [],   \
\                        %n r. r @ [f(n, nth(l, n))])"
end
