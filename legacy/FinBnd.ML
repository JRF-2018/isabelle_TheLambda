(*
    File:        FinBnd.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open FinBnd;

(** bnd_cont(D, h) : h is bound by D and is continuous **)

qed_goalw "bnd_contI" FinBnd.thy [bnd_cont_def]
    "[| !!X. [| X <= Pow(D); X ~= 0 |] ==> h(Union(X)) = (UN x: X. h(x));\
\       h(D) <= D |] ==> bnd_cont(D, h)"
  (fn prems =>
    [(rtac conjI 1),
     (rtac ballI 2),
     (rtac impI 2),
     (dtac PowD 2),
     (REPEAT (ares_tac prems 1))]);

qed_goalw "bnd_contD1" FinBnd.thy [bnd_cont_def]
    "bnd_cont(D, h) ==> h(D) <= D"
  (fn [hcont] =>
    [(rtac (hcont RS conjunct1) 1)]);

qed_goalw "bnd_contD2" FinBnd.thy [bnd_cont_def]
    "[| bnd_cont(D, h); X <= Pow(D); X ~= 0 |] ==> \
\          h(Union(X)) = (UN x: X. h(x))"
  (fn [hcont, dom_X, not_emptyX] =>
    [(rtac (hcont RS conjunct2 RS bspec RS mp) 1),
     (rtac (dom_X RS PowI) 1),
     (rtac not_emptyX 1)]);

qed_goalw "bnd_cont_upair" FinBnd.thy [Un_def]
    "[| bnd_cont(D, h); X <= D; Y <= D |] ==> h(X Un Y) = h(X) Un h(Y)"
  (fn [hcont, dom_x, dom_y] =>
    [(rtac (hcont RS bnd_contD2 RS ssubst) 1),
     (rtac subsetI 1),
     (rtac PowI 1),
     (etac UpairE 1),
     (etac ssubst 1),
     (etac ssubst 2),
     (rtac dom_x 1),
     (rtac dom_y 1),
     (rtac not_emptyI 1),
     (rtac UpairI1 1),
     (rtac equalityI 1),
     (ALLGOALS ((rtac Union_mono) THEN' (fast_tac ZF_cs)))]);

qed_goal "bnd_cont_bnd_mono" FinBnd.thy
    "bnd_cont(D, h) ==> bnd_mono(D,h)"
  (fn [hcont] =>
    [(rtac bnd_monoI 1),
     (rtac (hcont RS bnd_contD1) 1),
     (eres_inst_tac [("P", "%x. ?X <= h(x)")] 
    (subset_Un_iff RS iffD1 RS subst) 1),
     (res_inst_tac [("P", "%x. ?X <= x")] 
    (hcont RS bnd_cont_upair RS ssubst) 1),
     (REPEAT (ares_tac [Un_upper1] 1))]);


(** fin_bnd(x, h) : x is finitely bound by h **)

qed_goalw "fin_bnd_0" FinBnd.thy [fin_bnd_def]
    "fin_bnd(0, h)"
  (fn prems =>
    [(rtac (nat_0I RSN (2, bexI)) 1),
     (rtac empty_subsetI 1)]);

qed_goalw "fin_bnd_induct" FinBnd.thy [fin_bnd_def]
    "[| fin_bnd(a, h); P(0);\
\       !! x y. [| fin_bnd(x,h); y <= h(x); P(x)|]  ==> P(y) |] ==> P(a)"
  (fn [fb_a, P_0, indstep] =>
    [(rtac (fb_a RS bexE) 1),
     (eres_inst_tac [("P", "?A <= ?B(x)")] rev_mp 1),
     (rtac allE 1),
     (atac 2),
     (etac nat_induct 1),
     (rtac allI 1),
     (rtac (nat_rec_0 RS ssubst) 1),
     (rtac impI 1),
     (dtac (subset_empty_iff RS iffD1) 1),
     (etac ssubst 1),
     (rtac P_0 1),
     (rtac allI 1),
     (rtac (nat_rec_succ RS ssubst) 1),
     (atac 1),
     (rtac impI 1),
     (rtac indstep 1),
     (atac 2),
     (rtac bexI 1),
     (rtac subset_refl 1),
     (atac 1),
     (etac allE 1),
     (etac mp 1),
     (rtac subset_refl 1)]);

qed_goal "fin_bnd_lemma1" FinBnd.thy
    "[| bnd_mono(D, h); n: nat |] ==> nat_rec(n, 0, %n r. h(r)) <= D"
  (fn [hmono, prem] =>
    [(rtac (prem RS nat_induct) 1),
     (rtac (nat_rec_0 RS ssubst) 1),
     (rtac empty_subsetI 1),
     (etac (nat_rec_succ RS ssubst) 1),
     (rtac (hmono RS bnd_mono_subset) 1),
     (atac 1)]);

qed_goal "fin_bnd_lemma2" FinBnd.thy
    "[| bnd_mono(D, h); n: nat |] ==> \
\        nat_rec(n, 0, %l r. h(r)) <= nat_rec(succ(n), 0, %l r. h(r))"
  (fn [hmono, nnat] =>
    [(rtac (nnat RS nat_induct) 1),
     (rtac (nat_rec_0 RS ssubst) 1),
     (rtac empty_subsetI 1),
     (res_inst_tac [("P", "%x. x <= ?X")] (nat_rec_succ RS ssubst) 1),
     (res_inst_tac [("P", "%x. ?X <= x")] (nat_rec_succ RS ssubst) 2),
     (rtac (hmono RS bnd_monoD2) 3),
     (rtac (hmono RS fin_bnd_lemma1) 4),
     (REPEAT (ares_tac [nat_succI] 1))]);

val fin_bnd_lemma3 =
  let
    val res = prove_goal FinBnd.thy
        "bnd_mono(D,h) ==> ALL m: nat. ALL n: nat. n le m -->\
\              nat_rec(n, 0, %l r. h(r)) <= nat_rec(m, 0, %l r. h(r))"
      (fn [hmono] =>
        [(rtac ballI 1),
         (etac nat_induct 1),
         (rtac (impI RS ballI) 1),
         (dtac le_imp_subset 1),
         (dtac (subset_empty_iff RS iffD1) 1),
         (etac ssubst 1),
         (rtac subset_refl 1),
         (rtac (impI RS ballI) 1),
         (dtac (le_succ_iff RS iffD1) 1),
         (etac disjE 1),
         (rtac (hmono RS fin_bnd_lemma2 RSN (2, subset_trans)) 1),
         (atac 2),
         (etac ballE 1),
         (etac mp 1),
         (atac 1),
         (etac notE 1),
         (atac 1),
         (etac conjE 1),
         (etac ssubst 1),
         (rtac subset_refl 1)]);
   fun result () = res
  in
    standard(result() RS bspec RS bspec RS mp)
  end;

qed_goalw "fin_bnd_domain" FinBnd.thy [fin_bnd_def]
    "[| bnd_mono(D, h); fin_bnd(x, h) |] ==> x <= D"
  (fn [hmono, prem] =>
    [(rtac (prem RS bexE) 1),
     (etac subset_trans 1),
     (etac (hmono RS fin_bnd_lemma1) 1)]);

qed_goalw "fin_bnd_succ" FinBnd.thy [fin_bnd_def]
    "[| bnd_mono(D,h); fin_bnd(x, h); y <= h(x) |] ==> fin_bnd(y, h)"
  (fn [hmono, prem, bnd_y] =>
    [(rtac (prem RS bexE) 1),
     (rtac bexI 1),
     (rtac (nat_rec_succ RS ssubst) 1),
     (atac 1),
     (rtac (bnd_y RS subset_trans) 1),
     (rtac (hmono RS bnd_monoD2) 1),
     (REPEAT (ares_tac [nat_succI, hmono RS fin_bnd_lemma1] 1))]);

qed_goalw "fin_bnd_succ" FinBnd.thy [fin_bnd_def]
    "[| bnd_mono(D,h); fin_bnd(x, h); y <= h(x) |] ==> fin_bnd(y, h)"
  (fn [hmono, prem, bnd_y] =>
    [(rtac (prem RS bexE) 1),
     (rtac bexI 1),
     (rtac (nat_rec_succ RS ssubst) 1),
     (atac 1),
     (rtac (bnd_y RS subset_trans) 1),
     (rtac (hmono RS bnd_monoD2) 1),
     (REPEAT (ares_tac [nat_succI, hmono RS fin_bnd_lemma1] 1))]);

qed_goalw "fin_bnd_subset" FinBnd.thy [fin_bnd_def]
    "[| bnd_mono(D, h); fin_bnd(x, h); y <= x |] ==> fin_bnd(y, h)"
  (fn [hmono, fbnd, sb] =>
    [(rtac (fbnd RS bexE) 1),
     (rtac bexI 1),
     (atac 2),
     (etac (sb RS subset_trans) 1)]);

qed_goalw "fin_bnd_Un" FinBnd.thy [fin_bnd_def]
    "[| bnd_mono(D, h); fin_bnd(x, h); fin_bnd(y, h) |] ==>\
\                fin_bnd(x Un y, h)"
  (fn [hmono, f1, f2] =>
    [(rtac (f1 RS bexE) 1),
     (rtac (f2 RS bexE) 1),
     (rtac Ord_linear_le 1),
     (eres_inst_tac [("n", "xa")] nat_into_Ord 1),
     (eres_inst_tac [("n", "xaa")] nat_into_Ord 1),
     (rtac bexI 1),
     (rtac Un_least 1),
     (etac subset_trans 1),
     (etac subset_trans 2),
     (rtac (hmono RS fin_bnd_lemma3) 1),
     (atac 3),
     (rtac (hmono RS fin_bnd_lemma3) 3),
     (dres_inst_tac [("n", "xaa")] nat_into_Ord 5),
     (REPEAT (ares_tac [le_refl] 1)),
     (rtac bexI 1),
     (rtac Un_least 1),
     (etac subset_trans 1),
     (etac subset_trans 2),
     (rtac (hmono RS fin_bnd_lemma3) 1),
     (rtac (hmono RS fin_bnd_lemma3) 4),
     (atac 6),
     (dres_inst_tac [("n", "x")] nat_into_Ord 3),
     (REPEAT (ares_tac [le_refl] 1))]);

qed_goalw "fin_bnd_bound" FinBnd.thy [fin_bnd_def]
    "[| bnd_mono(D, h); fin_bnd(a, h); \
\       !!z. [| a <= h(z); z <= D; fin_bnd(h(z), h) |] ==> P |] ==> P"
  (fn [hmono, fb_a, fb_z] =>
    [(rtac (fb_a RS bexE) 1),
     (rtac fb_z 1),
     (etac subset_trans 1),
     (res_inst_tac [("P", "%x. ?X <= x"),
                  ("b", "%x r. h(r)")]
    (standard(nat_rec_succ RS subst)) 1),
     (rtac (hmono RS fin_bnd_lemma2) 2),
     (rtac (hmono RS fin_bnd_lemma1) 3),
     (rtac bexI 4),
     (res_inst_tac [("P", "%x. x <= ?X"),
                  ("b", "%x r. h(r)")]
    (standard(nat_rec_succ RS subst)) 4),
     (REPEAT (ares_tac [subset_refl, nat_succI] 1))]);

qed_goalw "fin_bnd_bound2" FinBnd.thy [fin_bnd_def]
    "[| bnd_mono(D, h); fin_bnd(a, h); \
\       !!z. [| a <= z; z <= h(z); z <= D; \
\               fin_bnd(z, h); fin_bnd(h(z), h) |] ==> P |] ==> P"
  (fn [hmono, fb_a, fb_z] =>
    [(rtac (fb_a RS bexE) 1),
     (rtac fb_z 1),
     (res_inst_tac [("P", "%x. ?X <= x"),
                  ("b", "%x r. h(r)")]
    (standard(nat_rec_succ RS subst)) 2),
     (rtac (hmono RS fin_bnd_lemma2) 3),
     (rtac (hmono RS fin_bnd_lemma1) 4),
     (rtac bexI 5),
     (rtac bexI 7),
     (res_inst_tac [("P", "%x. x <= ?X"),
                  ("b", "%x r. h(r)")]
    (standard(nat_rec_succ RS subst)) 7),
     (REPEAT (ares_tac [subset_refl, nat_succI] 1))]);

(** FinExt(D, h) : the finite extension of h **)

qed_goal "FinExt_bnd_cont" FinBnd.thy
    "bnd_cont(Pow(D), FinExt(D,h))"
  (fn _ =>
    [(rtac bnd_contI 1),
     (rewrite_goals_tac [FinExt_def]),
     (fast_tac ZF_cs 2),
     (rtac equalityI 1),
     (ALLGOALS (rtac subsetI)),
     (etac UnE 1),
     (etac not_emptyE 1),
     (fast_tac ZF_cs 1),
     (etac CollectE 1),
     (etac bexE 1),
     (etac UnionE 1),
     (etac UN_I 1),
     (rtac UnI2 1),
     (etac CollectI 1),
     (etac bexI 1),
     (atac 1),
     (etac UN_E 1),
     (etac UnE 1),
     (rtac UnI1 1),
     (atac 1),
     (rtac UnI2 1),
     (etac CollectE 1),
     (etac bexE 1),
     (etac CollectI 1),
     (etac bexI 1),
     (etac UnionI 1),
     (atac 1)]);

qed_goal "FinExt_bnd_mono" FinBnd.thy
    "bnd_mono(Pow(D), FinExt(D,h))"
  (fn _ =>
    [(rtac (FinExt_bnd_cont RS bnd_cont_bnd_mono) 1)]);

qed_goalw "FinExt_lower_Pow_lfp" FinBnd.thy [FinExt_def]
    "bnd_mono(D,h) ==> FinExt(D, h, Pow(lfp(D,h))) <= Pow(lfp(D,h))"
  (fn [hmono] =>
    [(rtac (Un_subset_iff RS iffD2) 1),
     (rtac conjI 1),
     (fast_tac ZF_cs 1),
     (rtac subsetI 1),
     (etac CollectE 1),
     (etac bexE 1),
     (REPEAT ((dtac PowD 1) ORELSE (rtac PowI 1))),
     (etac subset_trans 1),
     (rtac ((hmono RS lfp_lemma2) RSN (2, subset_trans)) 1),
     (rtac (hmono RS bnd_monoD2) 1),
     (REPEAT (ares_tac [lfp_subset] 1))]);

qed_goalw "FinExt_another_def" FinBnd.thy [FinExt_def]
    "[| bnd_mono(D,h); X <= Pow(D) |] \
\        ==> FinExt(D, h, X) = {0} Un (UN z: X. Pow(h(z)))"
  (fn [hmono, dom_X] =>
    [(rtac equalityI 1),
     (ALLGOALS (rtac (subset_refl RS Un_mono))),
     (ALLGOALS (rtac subsetI)),
     (REPEAT (eresolve_tac [CollectE, bexE] 1)),
     (rtac UN_I 1),
     (atac 1),
     (rtac PowI 1),
     (atac 1),
     (etac UN_E 1),
     (rtac CollectI 1),
     (dtac (dom_X RS subsetD) 1),
     (ALLGOALS (REPEAT o (dtac PowD))),
     (rtac PowI 1),
     (etac subset_trans 1),
     (etac (hmono RS bnd_mono_subset) 1),
     (rtac bexI 1),
     (REPEAT (atac 1))]);


(** fin_bnd_set and FinExt **)
qed_goalw "fin_bnd_set_domain" FinBnd.thy [fin_bnd_set_def]
    "fin_bnd_set(D, h) <= Pow(D)"
  (fn prems =>
    [(rtac Collect_subset 1)]);

qed_goalw "fin_bnd_set_0I" FinBnd.thy [fin_bnd_set_def]
    "0: fin_bnd_set(D, h)"
  (fn _ =>
    [(rtac CollectI 1),
     (rtac (empty_subsetI RS PowI) 1),
     (rtac fin_bnd_0 1)]);

qed_goalw "fin_bnd_setI" FinBnd.thy [fin_bnd_set_def]
    "[| a <= D; fin_bnd(a, h) |] ==> a: fin_bnd_set(D, h)"
  (fn [dom_a, fb_a] =>
    [(rtac (dom_a RS PowI RS CollectI) 1),
     (rtac fb_a 1)]);

qed_goalw "fin_bnd_setI2" FinBnd.thy [fin_bnd_set_def]
    "[| bnd_mono(D, h); fin_bnd(a, h) |] ==> a: fin_bnd_set(D, h)"
  (fn [hmono, fb_a] =>
    [(rtac ([hmono, fb_a] MRS fin_bnd_domain RS PowI RS CollectI) 1),
     (rtac fb_a 1)]);

qed_goalw "fin_bnd_setD1" FinBnd.thy [fin_bnd_set_def]
    "a: fin_bnd_set(D, h) ==> a <= D"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (fast_tac ZF_cs 1)]);

qed_goalw "fin_bnd_setD2" FinBnd.thy [fin_bnd_set_def]
    "a: fin_bnd_set(D, h) ==> fin_bnd(a, h)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (fast_tac ZF_cs 1)]);

qed_goalw "fin_bnd_setE" FinBnd.thy [fin_bnd_set_def]
    "[| a: fin_bnd_set(D, h); \
\        [| a <= D; fin_bnd(a, h)|] ==> P |] ==> P"
  (fn [fbs_a, prem] =>
    [(rtac (fbs_a RS CollectE) 1),
     (dtac PowD 1),
     (REPEAT (ares_tac [prem] 1))]);

qed_goalw "fin_bnd_set_subset_lfp_FinExt" FinBnd.thy [fin_bnd_set_def]
    "bnd_mono(D,h) ==> fin_bnd_set(D, h) <= lfp(Pow(D), FinExt(D, h))"
  (fn [hmono] =>
    [(rtac subsetI 1),
     (etac CollectE 1),
     (etac fin_bnd_induct 1),
     (rtac (FinExt_bnd_mono RS lfp_lemma2 RS subsetD) 1),
     (rtac (hmono RS FinExt_another_def RS ssubst) 1),
     (rtac lfp_subset 1),
     (rtac UnI1 1),
     (rtac singletonI 1),
     (rtac (FinExt_bnd_mono RS lfp_lemma2 RS subsetD) 1),
     (rtac (hmono RS FinExt_another_def RS ssubst) 1),
     (rtac lfp_subset 1),
     (rtac UnI2 1),
     (rtac UN_I 1),
     (rtac PowI 2),
     (atac 2),
     (atac 1)]);

qed_goalw "fin_bnd_set_pre_fixedpt" FinBnd.thy [fin_bnd_set_def]
    "bnd_mono(D, h) ==> FinExt(D, h, fin_bnd_set(D, h)) <= \
\       fin_bnd_set(D, h)"
  (fn [hmono] =>
    [(rtac (Collect_subset RS (hmono RS FinExt_another_def RS ssubst)) 1),
     (rtac subsetI 1),
     (etac UnE 1),
     (etac singletonE 1),
     (etac ssubst 1),
     (rtac CollectI 1),
     (rtac (empty_subsetI RS PowI) 1),
     (rtac fin_bnd_0 1),
     (etac UN_E 1),
     (etac CollectE 1),
     (rtac CollectI 1),
     (ALLGOALS (REPEAT o ((dtac PowD) ORELSE' (rtac PowI)))),
     (rtac (hmono RS bnd_monoD1 RSN (2, subset_trans)) 1),
     (etac subset_trans 1),
     (etac (hmono RS bnd_monoD2) 1),
     (rtac subset_refl 1),
     (etac (hmono RS fin_bnd_succ) 1),
     (atac 1)]);

qed_goal "fin_bnd_set_lfp_eq" FinBnd.thy
    "bnd_mono(D, h) ==> \
\       fin_bnd_set(D, h) = lfp(Pow(D), FinExt(D, h))"
  (fn [hmono] =>
    [(rtac equalityI 1),
     (rtac (hmono RS fin_bnd_set_subset_lfp_FinExt) 1),
     (rtac lfp_lowerbound 1),
     (rtac (hmono RS fin_bnd_set_pre_fixedpt) 1),
     (rtac fin_bnd_set_domain 1)]);

qed_goalw "fin_bnd_set_Pow_lfp_lowerbound" FinBnd.thy [fin_bnd_set_def]
    "bnd_mono(D,h) ==> fin_bnd_set(D, h) <= Pow(lfp(D,h))"
  (fn [hmono] =>
    [(rtac subsetI 1),
     (etac CollectE 1),
     (rtac PowI 1),
     (dtac PowD 1),
     (etac fin_bnd_induct 1),
     (rtac empty_subsetI 1),
     (rtac (hmono RS lfp_lemma2 RSN (2, subset_trans)) 1),
     (etac subset_trans 1),
     (rtac (hmono RS bnd_monoD2) 1),
     (atac 1),
     (rtac lfp_subset 1)]);

qed_goalw "Union_fin_bnd_set_pre_fixedpt" FinBnd.thy [fin_bnd_set_def]
    "bnd_cont(D, h) ==>\
\           h(Union(fin_bnd_set(D, h))) <= Union(fin_bnd_set(D, h))"
  (fn [hcont] =>
    [(res_inst_tac [("P", "%y. y <= ?X")] (hcont RS bnd_contD2 RS ssubst) 1),
     (rtac ((rewrite_rule [fin_bnd_set_def] fin_bnd_set_0I) RS not_emptyI) 2),
     (rtac Collect_subset 1),
     (rtac subsetI 1),
     (etac UN_E 1),
     (etac CollectE 1),
     (rtac UnionI 1),
     (rtac CollectI 1),
     (atac 3),
     (rtac (hcont RS bnd_cont_bnd_mono RS fin_bnd_succ) 2),
     (dtac PowD 1),
     (rtac PowI 1),
     (rtac (hcont RS bnd_cont_bnd_mono RS bnd_mono_subset) 1),
     (REPEAT (ares_tac [subset_refl] 1))]);

qed_goal "Union_fin_bnd_set_lfp_eq" FinBnd.thy
    "bnd_cont(D, h) ==> Union(fin_bnd_set(D, h)) = lfp(D, h)"
  (fn [hcont] =>
    [(rtac equalityI 1),
     (res_inst_tac [("P", "%x. ?X <= x")] (Union_Pow_eq RS subst) 1),
     (rtac (hcont RS bnd_cont_bnd_mono RS fin_bnd_set_Pow_lfp_lowerbound
          RS Union_mono) 1),
     (rtac lfp_lowerbound 1),
     (rtac (hcont RS Union_fin_bnd_set_pre_fixedpt) 1),
     (res_inst_tac [("P", "%x. ?X <= x")] (Union_Pow_eq RS subst) 1),
     (rtac (fin_bnd_set_domain RS Union_mono) 1)]);

qed_goal "fin_bnd_set_upper_Fin_lfp" FinBnd.thy
    "bnd_cont(D, h) ==> Fin(lfp(D, h)) <= fin_bnd_set(D, h)"
  (fn [hcont] =>
    [(rtac subsetI 1),
     (etac Fin_induct 1),
     (dres_inst_tac [("P", "%x. ?X: x")] 
    (hcont RS Union_fin_bnd_set_lfp_eq RS ssubst) 2),
     (etac UnionE 2),
     (rewrite_goals_tac [fin_bnd_set_def]),
     (rtac CollectI 1),
     (rtac (empty_subsetI RS PowI) 1),
     (rtac fin_bnd_0 1),
     (REPEAT ((etac CollectE 1) THEN (dtac PowD 1))),
     (rtac CollectI 1),
     (rtac (cons_subsetI RS PowI) 1),
     (DEPTH_SOLVE_1 ((etac subsetD 1) THEN (atac 1))),
     (atac 1),
     (rtac (hcont RS bnd_cont_bnd_mono RS fin_bnd_subset) 1),
     (res_inst_tac [("x", "B"), ("y", "y")] 
    (hcont RS bnd_cont_bnd_mono RS fin_bnd_Un) 1),
     (rtac (cons_eq RS subst) 3),
     (rtac Un_mono 3),
     (rtac singleton_subsetI 3),
     (REPEAT (ares_tac [subset_refl] 1))]);


(** Induction principles on finitely bound set **)
qed_goal "fin_bnd_set_Collect_is_pre_fixedpt" FinBnd.thy
    "[| mono_inj_pair(D,F,G); mono_inj_pair(F(D),Fp, Gp); F(G(0)) = 0;\
\       bnd_mono(D,h);\
\       !!x. x : FinExt(F(D), %x. F(h(G(x))),\
\                       {x: fin_bnd_set(F(D), %x. F(h(G(x)))).\
\                        (ALL y: Pow(Fp(F(G(x)))). P(Gp(y)))}) ==> P(x)\
\    |] ==> FinExt(F(D), %x. F(h(G(x))),\
\                       {x: fin_bnd_set(F(D), %x. F(h(G(x)))).\
\                        (ALL y: Pow(Fp(F(G(x)))). P(Gp(y)))})\
\             <= {x: fin_bnd_set(F(D), %x. F(h(G(x)))).\
\                        (ALL y: Pow(Fp(F(G(x)))). P(Gp(y)))}"
  (fn [hinj, hinjp, FG0, hmono, indstep] =>
    [(rtac subsetI 1),
     (rtac CollectI 1),
     (rtac (hmono RS (hinj RS mono_inj_pair_bnd_mono)
            RS (fin_bnd_set_pre_fixedpt RS subsetD)) 1),
     (rtac (FinExt_bnd_mono RS bnd_monoD2 RS subsetD) 1),
     (rtac fin_bnd_set_domain 2),
     (atac 2),
     (rtac Collect_subset 1),
     (rtac ballI 1),
     (dtac PowD 1),
     (rtac indstep 1),
     (rewrite_goals_tac [FinExt_def]),
     (etac UnE 1),
     (etac singletonE 1),
     (hyp_subst_tac 1),
     (rtac UnI1 1),
     (dtac (FG0 RS subst) 1),
     (dtac (hinjp RS mono_inj_pairD3) 1),
     (rtac (hinjp RS mono_inj_pairD2) 1),
     (rtac (make_elim (hinjp RS mono_inj_pairD1 RS subst)) 3),
     (atac 4),
     (dtac (subset_empty_iff RS iffD1) 4),
     (etac ssubst 4),
     (REPEAT (ares_tac [empty_subsetI, subset_refl, singletonI] 1)),
     (etac CollectE 1),
     (etac bexE 1),
     (etac CollectE 1),
     (rtac UnI2 1),
     (rtac CollectI 1),
     (rtac bexI 2),
     (rtac CollectI 3),
     (rtac ballI 4),
     (etac bspec 4),
     (atac 4),
     (rtac PowI 1),
     (dtac PowD 1),
     (rtac subset_trans 1),
     (rtac (hinjp RS mono_inj_pairD3) 1),
     (atac 1),
     (rtac (hinjp RS mono_inj_pairD2) 1),
     (rtac (hinjp RS mono_inj_pairD1 RS ssubst) 3),
     (rtac subset_trans 5),
     (rtac (hinj RS mono_inj_pairD2) 6),
     (res_inst_tac [("P", "%x. ?X <= x")] 
         (hinj RS mono_inj_pairD1 RS subst) 6),
     (rtac (hinj RS mono_inj_pairD3) 7),
     (atac 7),
     (res_inst_tac [("P", "%x. ?X <= x")] 
           (hinjp RS mono_inj_pairD1 RS subst) 5),
     (rtac (hinjp RS mono_inj_pairD3) 6),
     (rtac (hinjp RS mono_inj_pairD2) 7),
     (rtac (hinj RS mono_inj_pairD2) 10),
     (TRYALL (ares_tac [subset_refl])),
     (TRYALL (fn i=>
         (TRY (dtac PowD i)) THEN
         (rtac (hinj RS mono_inj_pairD2) i) THEN
         (rtac subset_refl (i + 1)) THEN
         (res_inst_tac [("P", "%x. ?X <= x")]
          (subset_refl RS (hinj RS mono_inj_pairD1 RS subst)) i) THEN
         (rtac (hinj RS mono_inj_pairD3) i) THEN
         (rtac subset_refl (i + 1)) THEN
         (atac i))),
     (TRYALL (fn i=>
            (rtac (hmono RS bnd_mono_subset) i) THEN
            (res_inst_tac [("P", "%x. ?X <= x")]
             (hinj RS mono_inj_pairD1 RS subst) i) THEN
            (rtac subset_refl i) THEN
            (rtac (hinj RS mono_inj_pairD3) i) THEN
            (rtac subset_refl (i + 1)) THEN
            (rtac PowD i) THEN
            (etac (fin_bnd_set_domain RS subsetD) i)))]);

qed_goal "fin_bnd_set_induct_lemma1" FinBnd.thy
    "[| mono_inj_pair(D,F,G); mono_inj_pair(F(D),Fp, Gp); F(G(0)) = 0;\
\       bnd_mono(D,h); P(0); \
\       !!x. [| x <= F(D); EX z: fin_bnd_set(F(D), %x. F(h(G(x)))). \
\               x <= F(h(G(z))) & \
\               (ALL y. y <= Fp(F(G(z))) --> P(Gp(y))) |] ==> P(x) \
\    |] ==> fin_bnd_set(F(D), %x. F(h(G(x)))) <= \
\                    {x: fin_bnd_set(F(D), %x. F(h(G(x)))). \
\                                     ALL y: Pow(Fp(F(G(x)))). P(Gp(y))}"
  (fn [hinj, hinjp, FG0, hmono, P0, indstep] =>
    [(res_inst_tac [("P", "%x. x <= ?X")]
    ([hinj, hmono] MRS mono_inj_pair_bnd_mono RS fin_bnd_set_lfp_eq RS
     ssubst) 1),
     (rtac lfp_lowerbound 1),
     (rtac ([hinjp, FG0, hmono] MRS 
          (hinj RS fin_bnd_set_Collect_is_pre_fixedpt)) 1),
     (rtac (Collect_subset RS subset_trans) 2),
     (rtac fin_bnd_set_domain 2),
     (rewrite_goals_tac [FinExt_def]),
     (rtac indstep 1),
     (ALLGOALS (etac UnE)),
     (TRYALL ((etac singletonE) THEN' (hyp_subst_tac))),
     (TRYALL ((etac CollectE) THEN' (etac bexE) THEN' (etac CollectE))),
     (rtac bexI 3),
     (rtac conjI 3),
     (rtac (impI RS allI) 4),
     (dtac (hinjp RS mono_inj_pairD3) 4),
     (rtac ssubst 5),
     (rtac P0 6),
     (rtac (subset_empty_iff RS iffD1) 5),
     (res_inst_tac [("P", "%x. ?X <= x")] (FG0 RS subst) 5),
     (res_inst_tac [("P", "%x. ?X <= x")] (hinjp RS mono_inj_pairD1 
                                         RS subst) 5),
     (atac 6),
     (res_inst_tac [("P", "%x. x <= ?X")] (FG0 RS ssubst) 5),
     (res_inst_tac [("P", "%x. Fp(x) <= ?X")] (FG0 RS ssubst) 4),
     (rtac (hinjp RS mono_inj_pairD2) 4),
     (dtac PowD 2),
     (REPEAT (ares_tac [empty_subsetI, subset_refl] 1)),
     (rtac bexI 2),
     (rtac conjI 2),
     (rtac (impI RS allI) 3),
     (etac bspec 3),
     (rtac PowI 3),
     (REPEAT (atac 2)),
     (rewrite_goals_tac [fin_bnd_set_def]),
     (rtac CollectI 1),
     (rtac (empty_subsetI RS PowI) 1),
     (rtac fin_bnd_0 1)]);

qed_goal "mono_inj_pair_fin_bnd_set_induct" FinBnd.thy
    "[| mono_inj_pair(D,F,G); mono_inj_pair(F(D),Fp, Gp); \
\       F(G(0)) = 0; \
\       bnd_mono(D,h); a: fin_bnd_set(F(D), %x. F(h(G(x)))); P(0);  \
\       !!x. [| x <= F(D); EX z: fin_bnd_set(F(D), %x. F(h(G(x)))). \
\               x <= F(h(G(z))) & \
\               (ALL y. y <= Fp(F(G(z))) --> P(Gp(y))) |] ==> P(x) \
\    |] ==> P(a)"
  (fn [hinj, hinjp, FG0, hmono, a_in_fb, P0, indstep] =>
    [(rtac ((hinjp RS mono_inj_pairD1) RS subst) 1),
     (rtac ((a_in_fb RS (fin_bnd_set_domain RS subsetD)) RS PowD) 1),
     (rtac ((rewrite_rule [fin_bnd_set_def] a_in_fb) RS CollectD2
             RS ([hinj, hmono] MRS mono_inj_pair_bnd_mono
                        RS fin_bnd_bound)) 1),
     (rtac ([hinjp, FG0, hmono] MRS 
            (hinj RS fin_bnd_set_induct_lemma1) RS
            subsetD RS CollectD2 RS bspec) 1),
     (rtac PowI 4),
     (rtac (hinjp RS mono_inj_pairD2) 4),
     (rtac (hinj RS mono_inj_pairD2) 5),
     (res_inst_tac [("P", "%x. ?X <= x")] 
      (hinj RS mono_inj_pairD1 RS subst) 5),
     (rtac (hinj RS mono_inj_pairD3) 6),
     (SELECT_GOAL (rewrite_goals_tac [fin_bnd_set_def]) 3),
     (rtac CollectI 3),
     (atac 4),
     (rtac PowI 3),
     (res_inst_tac [("P", "%x. ?X <= F(x)")]
      (hinj RS mono_inj_pairD1 RS ssubst) 4),
     (rtac ([hinj, hmono] MRS mono_inj_pair_bnd_mono RS bnd_mono_subset) 3),
     (rtac ([hinj, hmono] MRS mono_inj_pair_bnd_mono RS bnd_mono_subset) 7),
     (rtac (hmono RS bnd_mono_subset) 4),
     (res_inst_tac [("P", "%x. ?X <= x")]
      (hinj RS mono_inj_pairD1 RS subst) 4),
     (rtac (hinj RS mono_inj_pairD3) 5),
     (REPEAT (ares_tac [subset_refl, P0, indstep] 1))]);

val fin_bnd_set_induct = standard([trivial_mono_inj_pair, refl] MRS
                                  (trivial_mono_inj_pair RS
                                   mono_inj_pair_fin_bnd_set_induct));

qed_goal "mono_inj_pair_fin_bnd_lemma" FinBnd.thy
    "[| mono_inj_pair(D, F, G); bnd_mono(D, h); \
\       fin_bnd(z, %x. F(h(G(x)))) |] ==> \
\        fin_bnd(F(G(z)), %x. F(h(G(x))))"
  (fn [hinj, hmono, prem] =>
    [(rtac ([[hinj, hmono] MRS mono_inj_pair_bnd_mono, prem] 
          MRS fin_bnd_bound2) 1),
     (rtac ([hinj, hmono] MRS mono_inj_pair_bnd_mono RS fin_bnd_succ) 1),
     (rtac (hinj RS mono_inj_pairD2) 2),
     (res_inst_tac [("P", "%x. ?X <= x")] 
    (hinj RS mono_inj_pairD1 RS subst) 2),
     (rtac (hinj RS mono_inj_pairD3) 3),
     (etac subset_trans 3),
     (atac 3),
     (atac 1),
     (rtac (hinj RS mono_inj_pairD2) 2),
     (rtac subset_refl 3),
     (REPEAT ((rtac (hmono RS bnd_mono_subset) 1) THEN
            (res_inst_tac [("P", "%x. ?X <= x")] 
             (hinj RS mono_inj_pairD1 RS subst) 1) THEN
            (rtac (hinj RS mono_inj_pairD3) 2) THEN
            (REPEAT (ares_tac [subset_refl] 1))))]);

qed_goal "fin_bnd_set_0I" FinBnd.thy
    "0: fin_bnd_set(D, h)"
  (fn prems =>
    [(rtac fin_bnd_setI 1),
     (rtac empty_subsetI 1),
     (rtac fin_bnd_0 1)]);

qed_goal "fin_bnd_set_succI" FinBnd.thy
    "[| bnd_mono(D, h); Y <= h(X); X: fin_bnd_set(D, h) |] \
\         ==> Y: fin_bnd_set(D, h)"
  (fn [hmono, major, prem] =>
    [(rtac (hmono RS fin_bnd_setI2) 1),
     (rtac ([hmono, prem RS fin_bnd_setD2] MRS fin_bnd_succ) 1),
     (rtac major 1)]);

qed_goal "fin_bnd_set_UnI" FinBnd.thy
    "[| bnd_mono(D, h); X: fin_bnd_set(D,h); Y: fin_bnd_set(D, h) |] \
\         ==> X Un Y: fin_bnd_set(D, h)"
  (fn [hmono, prem1, prem2] =>
    [(rtac (hmono RS fin_bnd_setI2) 1),
     (rtac (hmono RS fin_bnd_Un) 1),
     (rtac (prem1 RS fin_bnd_setD2) 1),
     (rtac (prem2 RS fin_bnd_setD2) 1)]);

qed_goal "fin_bnd_set_subsetI" FinBnd.thy
    "[| bnd_mono(D, h); Y <= X; X: fin_bnd_set(D,h) |] \
\         ==> Y: fin_bnd_set(D, h)"
  (fn [hmono, major, prem] =>
    [(rtac (hmono RS fin_bnd_setI2) 1),
     (rtac ([hmono, prem RS fin_bnd_setD2, major] MRS fin_bnd_subset) 1)]);

qed_goal "fin_bnd_set_boundE" FinBnd.thy
    "[| bnd_mono(D, h); a: fin_bnd_set(D, h); \
\       !!z. [| a <= z; z <= h(z); z: fin_bnd_set(D, h); \
\               h(z): fin_bnd_set(D, h) |] ==> P |] ==> P"
  (fn hmono::major::prems =>
    [(rtac ([hmono, major RS fin_bnd_setD2] MRS fin_bnd_bound2) 1),
     (resolve_tac prems 1),
     (REPEAT (ares_tac [hmono RS fin_bnd_setI2] 1))]);
