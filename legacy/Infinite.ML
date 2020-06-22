(*
    File:        Infinite.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open Infinite;

qed_goalw "InfiniteI" Infinite.thy [Infinite_def]
    "[| !! x. [| x: Fin(X); x = X |] ==> False |] ==> Infinite(X)"
  (fn [prem] =>
    [(fast_tac (ZF_cs addIs [prem]) 1)]);

qed_goalw "Infinite_imp_not_empty" Infinite.thy [Infinite_def]
    "Infinite(X) ==> X ~= 0"
  (fn [prem] =>
    [(rtac (prem RS bspec) 1),
     (resolve_tac Fin.intrs 1)]);

qed_goalw "InfiniteD" Infinite.thy [Infinite_def]
    "[| Infinite(X); F: Fin(X) |] ==> EX z: X. z ~: F"
  (fn [major, prem] =>
    [(cut_facts_tac [[major, prem] MRS bspec, prem RS FinD] 1),
     (rtac swap 1),
     (rtac notI 1),
     (etac notE 1),
     (rtac equalityI 1),
     (REPEAT (atac 1)),
     (rtac subsetI 1),
     (rtac swap 1),
     (rtac bexI 2),
     (REPEAT (atac 1))]);

val InfiniteE = standard (InfiniteD RS bexE);
