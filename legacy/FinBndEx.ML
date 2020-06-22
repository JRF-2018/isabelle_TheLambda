(*
    File:        FinBndEx.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open FinBndEx;

qed_goal "subset_consE" ZF.thy
    "[| x <= cons(a, B); a: x ==> R; x <= B ==> R |] ==> R"
  (fn [major, prem1, prem2] =>
    [(rtac (excluded_middle RS disjE) 1),
     (etac prem1 2),
     (rtac prem2 1),
     (rtac subsetI 1),
     (forward_tac [major RS subsetD] 1),
     (etac consE 1),
     (hyp_subst_tac 1),
     (etac notE 1),
     (REPEAT (atac 1))]);

qed_goalw "subset_succE" ZF.thy [succ_def]
    "[| x <= succ(n); n: x ==> R; x <= n ==> R |] ==> R"
  (fn prems =>
    [(rtac subset_consE 1),
     (REPEAT ((eresolve_tac prems 1) ORELSE (resolve_tac prems 1)))]);

qed_goalw "succ_self_neq" ZF.thy [succ_def]
    "succ(n) = n ==> P"
  (fn [prem] =>
    [(rtac mem_irrefl 1),
     (rtac (prem RS equalityD1 RS subsetD) 1),
     (rtac consI1 1)]);

qed_goalw "h_nat_bnd_mono" FinBndEx.thy [bnd_mono_def, h_nat_def]
    "bnd_mono(Inf, h_nat)"
  (fn _ =>
    [(rtac (rewrite_rule [bnd_mono_def] nat_bnd_mono) 1)]);

qed_goalw "h_nat_lfp" FinBndEx.thy [lfp_def, h_nat_def, nat_def]
    "nat = lfp(Inf, h_nat)"
  (fn _ =>
    [(rtac refl 1)]);

qed_goal "h_tn_bnd_mono" FinBndEx.thy
    "bnd_mono(succ(nat), h_tn)"
  (fn _ =>
    [(rtac bnd_monoI 1),
     (rewrite_goals_tac [h_tn_def]),
     (rtac (if_P RS ssubst) 1),
     (rtac (succI1 RS disjI1) 1),
     (rtac subset_refl 1),
     (res_inst_tac [("P1", "%x. ?X <= x")] (expand_if RS iffD2) 1),
     (rtac conjI 1),
     (rtac impI 1),
     (res_inst_tac [("P1", "%x. x <= ?X")] (expand_if RS iffD2) 1),
     (rtac conjI 1),
     (rtac (subset_refl RS impI) 1),
     (rtac impI 1),
     (etac subset_succE 1),
     (etac notE 1),
     (etac disjI1 1),
     (rtac (subset_succI RSN (2, subset_trans)) 1),
     (rtac (h_nat_lfp RS ssubst) 1),
     (rtac (h_nat_bnd_mono RS lfp_lemma2 RSN (2, subset_trans)) 1),
     (rtac (h_nat_bnd_mono RS bnd_monoD2) 1),
     (etac (h_nat_lfp RS subst) 1),
     (rtac lfp_subset 1),
     (rtac impI 1),
     (res_inst_tac [("P1", "%x. x <= ?X")] (expand_if RS iffD2) 1),
     (rtac conjI 1),
     (rtac impI 1),
     (etac notE 1),
     (etac disjE 1),
     (rtac disjI1 1),
     (etac subsetD 1),
     (atac 1),
     (hyp_subst_tac 1),
     (eres_inst_tac [("x", "X")] subset_succE 1),
     (etac disjI1 1),
     (REPEAT (ares_tac [disjI2, equalityI] 1)),
     (rtac impI 1),
     (etac (h_nat_bnd_mono RS bnd_monoD2) 1),
     (eres_inst_tac [("x", "X")] subset_succE 1),
     (etac notE 1),
     (etac disjI1 1),
     (etac subset_trans 1),
     (rtac (h_nat_lfp RS ssubst) 1),
     (rtac lfp_subset 1)]);

qed_goal "h_tn_lfp" FinBndEx.thy
    "lfp(succ(nat), h_tn) = succ(nat)"
  (fn _ =>
    [(rtac (h_tn_bnd_mono RS lfpI) 1),
     (rewrite_goals_tac [h_tn_def]),
     (dres_inst_tac [("P1", "%x. x <= ?X")] (expand_if RS iffD1) 1),
     (etac conjE 1),
     (res_inst_tac [("Q", "nat: X | X = nat")] (excluded_middle RS disjE) 1),
     (dtac mp 1),
     (etac subset_succE 1),
     (etac notE 1),
     (etac disjI1 1),
     (rtac notE 1),
     (atac 1),
     (mp_tac 1),
     (rtac disjI2 1),
     (rtac equalityI 1),
     (atac 1),
     (rtac (h_nat_lfp RS ssubst) 1),
     (etac lfp_lowerbound 1),
     (etac subset_trans 1),
     (rtac (h_nat_lfp RS ssubst) 1),
     (rtac lfp_subset 1),
     (mp_tac 1),
     (atac 1),
     (rtac (if_P RS ssubst) 1),
     (rtac (succI1 RS disjI1) 1),
     (mp_tac 1),
     (atac 1),
     (rtac (if_P RS ssubst) 1),
     (rtac (succI1 RS disjI1) 1),
     (rtac subset_refl 1)]);

qed_goal "FinBndEx_lemma1" FinBndEx.thy
    "n: A ==> ~(A: n | n = A)"
  (fn [prem] =>
    [(rtac notI 1),
     (etac disjE 1),
     (etac (prem RS mem_asym) 1),
     (cut_facts_tac [prem] 1),
     (hyp_subst_tac 1),
     (etac mem_irrefl 1)]);

qed_goalw "FinBndEx_lemma2" FinBndEx.thy [h_nat_def]
    "n: nat ==> nat_rec(n, 0, %n r. h_nat(r)) = n"
  (fn [prem] =>
    [(rtac (prem RS nat_induct) 1),
     (simp_tac (nat_ss addsimps [nat_rec_0, nat_rec_succ]) 1),
     (asm_simp_tac (nat_ss addsimps [nat_rec_0, nat_rec_succ]) 1),
     (rtac equalityI 1),
     (rtac subsetI 1),
     (etac UnE 1),
     (etac singletonE 1),
     (hyp_subst_tac 1),
     (rtac ltD 1),
     (etac (nat_into_Ord RS Ord_0_le) 1),
     (etac RepFunE 1),
     (hyp_subst_tac 1),
     (rtac ltD 1),
     (etac (ltI RS succ_leI) 1),
     (etac nat_into_Ord 1),
     (rtac subsetI 1),
     (forw_inst_tac [("i", "xa")] ltI 1),
     (etac (nat_into_Ord RS Ord_succ) 1),
     (forward_tac [lt_nat_in_nat] 1),
     (etac nat_succI 1),
     (eres_inst_tac [("n", "xa")] natE 1),
     (hyp_subst_tac 1),
     (fast_tac ZF_cs 1),
     (rtac UnI2 1),
     (hyp_subst_tac 1),
     (rtac RepFunI 1),
     (rtac ltD 1),
     (rtac succ_leE 1),
     (etac ltI 1),
     (etac (nat_into_Ord RS Ord_succ) 1)]);

qed_goalw "FinBndEx_lemma3" FinBndEx.thy [h_tn_def]
    "n: nat ==> nat_rec(n, 0, %x r. h_tn(r)) = nat_rec(n, 0, %x r. h_nat(r))"
  (fn [prem] =>
    [(rtac (prem RS nat_induct) 1),
     (simp_tac (nat_ss addsimps [nat_rec_0, nat_rec_succ]) 1),
     (asm_simp_tac (nat_ss addsimps [nat_rec_0, nat_rec_succ]) 1),
     (asm_full_simp_tac (IFOL_ss addsimps [FinBndEx_lemma2])  1),
     (etac (FinBndEx_lemma1 RS if_not_P RS ssubst) 1),
     (rtac refl 1)]);

qed_goal "Singleton_of_the_nat_is_an_finite_subset_of_succ_nat" FinBndEx.thy
    "{nat}: Fin(lfp(succ(nat), h_tn))"
  (fn _ =>
    [(res_inst_tac [("P", "%x. ?X: Fin(x)")] (h_tn_lfp RS ssubst) 1),
     (resolve_tac Fin.intrs 1),
     (rtac succI1 1),
     (resolve_tac Fin.intrs 1)]);

qed_goal "Singleton_of_the_nat_is_not_in_the_finitely_bound_set" FinBndEx.thy
    "{nat} ~: fin_bnd_set(succ(nat), h_tn)"
  (fn _ =>
    [(rtac notI 1),
     (etac fin_bnd_setE 1),
     (rewrite_goals_tac [fin_bnd_def]),
     (etac bexE 1),
     (eres_inst_tac [("P", "?X <= nat_rec(?x, ?y, ?H)")] rev_mp 1),
     (asm_simp_tac (IFOL_ss addsimps [FinBndEx_lemma2, FinBndEx_lemma3]) 1),
     (rtac notI 1),
     (dres_inst_tac [("C", "n")] singleton_subsetD 1),
     (etac mem_asym 1),
     (atac 1)]);

qed_goal "h_nat_bnd_cont" FinBndEx.thy
    "bnd_cont(Inf, h_nat)"
  (fn _ =>
    [(rtac bnd_contI 1),
     (rtac (h_nat_bnd_mono RS bnd_monoD1) 2),
     (rewrite_goals_tac [h_nat_def]),
     (rtac equalityI 1),
     (fast_tac ZF_cs 2),
     (rtac subsetI 1),
     (etac UnE 1),
     (etac singletonE 1),
     (hyp_subst_tac 1),
     (etac not_emptyE 1),
     (etac UN_I 1),
     (rtac (singletonI RS UnI1) 1),
     (etac RepFunE 1),
     (etac UnionE 1),
     (etac UN_I 1),
     (rtac UnI2 1),
     (hyp_subst_tac 1),
     (rtac RepFunI 1),
     (atac 1)]);

qed_goalw "nat_not_in_the_fin_bnd_set" FinBndEx.thy 
           [fin_bnd_set_def, fin_bnd_def]
    "nat ~: fin_bnd_set(Inf, h_nat)"
  (fn _ =>
    [(rtac notI 1),
     (etac CollectE 1),
     (etac bexE 1),
     (asm_full_simp_tac (IFOL_ss addsimps [FinBndEx_lemma2]) 1),
     (rtac (mem_imp_not_eq RS notE) 1),
     (rtac equalityI 2),
     (atac 3),
     (etac (ltI RS leI RS le_imp_subset) 2),
     (rtac Ord_nat 2),
     (atac 1)]);

qed_goal "Pow_lfp_of_h_nat_is_not_equal_to_the_fin_bnd_set" FinBndEx.thy
    "Pow(lfp(Inf, h_nat)) ~= fin_bnd_set(Inf, h_nat)"
  (fn _ =>
    [(rtac notI 1),
     (rtac (nat_not_in_the_fin_bnd_set RS notE) 1),
     (etac subst 1),
     (rtac PowI 1),
     (rtac (h_nat_lfp RS subst) 1),
     (rtac subset_refl 1)]);
