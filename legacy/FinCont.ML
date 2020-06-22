(*
    File:        FinCont.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open FinCont;

qed_goal "Union_UN_eq" ZF.thy
    "Union(UN x: X. F(x)) = (UN x: X. Union(F(x)))"
  (fn prems =>
    [(fast_tac eq_cs 1)]);

val Fin_subset_lemma2 =
  let
    val res = prove_goal Finite.thy
        "a: Fin(A) ==> a <= B --> a: Fin(B)"
      (fn prems =>
        [(rtac (hd(prems) RS Fin_induct) 1),
         (rtac impI 1),
         (rtac Fin.emptyI 1),
         (rtac impI 1),
         (etac cons_subsetE 1),
         (rtac Fin.consI 1),
         (etac mp 2),
         (REPEAT (atac 1))]);
   fun result () = res
  in
    result() RS mp
  end;

val prems = goalw FinCont.thy [fin_cont_def]
    "[| !!X Y. [| X <= D; Y <= D |] ==> h(X Un Y) = h(X) Un h(Y);\
\	h(0): Fin(D);\
\	!!x. x: D ==> h({x}): Fin(h(D)) \
\    |] ==> fin_cont(D, h)";
