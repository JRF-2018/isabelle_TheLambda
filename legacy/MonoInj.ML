(*
    File:        MonoInj.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open MonoInj;

qed_goal "lfpI" Fixedpt.thy
    "[| bnd_mono(D,h); \
    \   !!X. [| X <= D;  h(X) <= X |] ==> A <= X; \
    \   h(A) <= A \
    \|]==> lfp(D,h) = A"
  (fn [hmono, lb, pfp] =>
    [(rtac equalityI 1),
     (rtac lfp_lowerbound 1),
     (rtac pfp 1),
     (rtac lb 1),
     (TRYALL (ares_tac [subset_refl, hmono RS bnd_monoD1])),
     (rtac lfp_greatest 1),
     (rtac lb 2),
     (TRYALL (ares_tac [hmono RS bnd_monoD1]))]);


(** Monotonic injection pairs **)

qed_goalw "mono_inj_pairI" MonoInj.thy [mono_inj_pair_def]
    "[| !!x. x <= D ==> G(F(x)) = x; \
    \   !!x y. [| x <= y; y <= D |] ==> F(x) <= F(y); \
    \   !!x y. [| x <= y; y <= F(D) |] ==> G(x) <= G(y) \
    \|] ==> mono_inj_pair(D,F,G)"
  (fn prems =>
    [(REPEAT_FIRST (rtac conjI)),
     (ALLGOALS (REPEAT o (rtac allI))),
     (ALLGOALS (rtac impI)),
     (TRYALL (etac conjE)),
     (REPEAT (ares_tac prems 1))]);

qed_goalw "mono_inj_pairD1" MonoInj.thy [mono_inj_pair_def]
    "[| mono_inj_pair(D,F,G); x <= D |] ==> G(F(x)) = x"
  (fn prems =>
    [(cut_facts_tac (prems RL [conjunct1]) 1),
     (etac allE 1),
     (etac mp 1),
     (resolve_tac prems 1)]);

qed_goalw "mono_inj_pairD2" MonoInj.thy [mono_inj_pair_def]
    "[| mono_inj_pair(D,F,G); x <= y; y <= D |] ==> F(x) <= F(y)"
  (fn major::prems =>
    [(cut_facts_tac [major RS (conjunct2 RS conjunct1)] 1),
     (REPEAT (eresolve_tac [allE, mp] 1)),
     (rtac conjI 1),
     (REPEAT (ares_tac prems 1))]);

qed_goalw "mono_inj_pairD3" MonoInj.thy [mono_inj_pair_def]
    "[| mono_inj_pair(D,F,G); x <= y; y <= F(D) |] ==> G(x) <= G(y)"
  (fn major::prems =>
    [(cut_facts_tac [major RS (conjunct2 RS conjunct2)] 1),
     (REPEAT (eresolve_tac [allE, mp] 1)),
     (rtac conjI 1),
     (REPEAT (ares_tac prems 1))]);


(** Lfp theorems for monotonic injection pairs **)

qed_goal "mono_inj_pair_lfp_subset" MonoInj.thy
    "mono_inj_pair(D,F,G) ==> F(lfp(D,h)) <= F(D)"
  (fn [hinj] =>
    [(rtac (hinj RS mono_inj_pairD2) 1),
     (rtac lfp_subset 1),
     (rtac subset_refl 1)]);

qed_goal "mono_inj_pair_bnd_mono" MonoInj.thy
    "[| mono_inj_pair(D,F,G); bnd_mono(D,h) |] \
    \ ==> bnd_mono(F(D), %X. F(h(G(X))))"
  (fn [hinj,hmono] =>
    [(rtac bnd_monoI 1),
     (rtac (hinj RS mono_inj_pairD2) 2),
     (rtac (hmono RS bnd_monoD2) 2),
     (rtac (hinj RS mono_inj_pairD3) 2),
     (rtac (hinj RS mono_inj_pairD1 RS ssubst) 1),
     (rtac (hinj RS mono_inj_pairD2) 2),
     (TRYALL (ares_tac [subset_refl, hmono RS bnd_monoD1])),
     (ALLGOALS (fn i=>
	      (forw_inst_tac [("x", "X")] (hinj RS mono_inj_pairD3) i) THEN
	      (rtac (hinj RS mono_inj_pairD2) i))),
     (rtac (hinj RS mono_inj_pairD1 RS subst) 3),
     (rtac (hmono RS bnd_mono_subset) 7),
     (rtac (hinj RS mono_inj_pairD1 RS subst) 7),
     (ALLGOALS (ares_tac [subset_refl]))]);

qed_goal "mono_inj_pair_pre_fixedpt" MonoInj.thy
    "[| mono_inj_pair(D,F,G); bnd_mono(D,h) |] \
     \ ==> F(h(G(F(lfp(D,h))))) <= F(lfp(D,h))"
  (fn [hinj,hmono] =>
    [(rtac (hinj RS mono_inj_pairD2) 1),
     (rtac (hinj RS mono_inj_pairD1 RS ssubst) 1),
     (REPEAT (ares_tac [lfp_subset, hmono RS lfp_lemma2] 1))]);

qed_goal "mono_inj_pair_lfp_lemma1" MonoInj.thy
    "[| mono_inj_pair(D,F,G); bnd_mono(D,h); X <= F(D); F(h(G(X))) <= X |]\
     \  ==> h(h(G(X))) <= h(G(X))"
  (fn [hinj, hmono, dom_x, x_is_pfp] =>
    [(res_inst_tac [("P", "%x. h(x) <= ?X")]
      (hinj RS mono_inj_pairD1 RS subst) 1),
     (rtac (hmono RS bnd_monoD2) 2),
     (rtac (hinj RS mono_inj_pairD3) 2),
     (rtac (hmono RS bnd_mono_subset) 1),
     (rtac (hinj RS mono_inj_pairD1 RS subst) 4),
     (rtac (hinj RS mono_inj_pairD3) 5),
     (rtac (hinj RS mono_inj_pairD1 RS subst) 1),
     (rtac (hinj RS mono_inj_pairD3) 2),
     (REPEAT (ares_tac [subset_refl, dom_x, x_is_pfp] 1))]);

qed_goal "mono_inj_pair_lfp_lowerbound" MonoInj.thy
    "[| mono_inj_pair(D,F,G); bnd_mono(D,h); X <= F(D); F(h(G(X))) <= X |]\
     \  ==> F(lfp(D,h)) <= X"
  (fn prems as [hinj, hmono, dom_x, x_is_pfp] =>
    [(rtac (x_is_pfp RSN (2, subset_trans)) 1),
     (rtac (hinj RS mono_inj_pairD2) 1),
     (rtac lfp_lowerbound 1),
     (rtac (hmono RS bnd_mono_subset) 2),
     (rtac (hmono RS bnd_mono_subset) 3),
     (rtac (hinj RS mono_inj_pairD1 RS subst) 2),
     (rtac (hinj RS mono_inj_pairD1 RS subst) 4),
     (rtac (hinj RS mono_inj_pairD3) 3),
     (rtac (hinj RS mono_inj_pairD3) 6),
     (rtac (hmono RS (hinj RS mono_inj_pair_lfp_lemma1)) 1),
     (REPEAT (ares_tac (prems @ [subset_refl]) 1))]);

qed_goal "mono_inj_pair_lfp_eq" MonoInj.thy
    "[| mono_inj_pair(D,F,G); bnd_mono(D,h) |]\
     \  ==> lfp(F(D), %X. F(h(G(X)))) = F(lfp(D,h))"
  (fn prems =>
    [(rtac lfpI 1),
     (REPEAT (ares_tac (prems @ ([prems] MRL [mono_inj_pair_bnd_mono,
			      mono_inj_pair_pre_fixedpt,
			      mono_inj_pair_lfp_lowerbound])) 1))]);

qed_goal "trivial_mono_inj_pair" MonoInj.thy
    "mono_inj_pair(D, %x. x, %x. x)"
  (fn prems =>
    [(rtac mono_inj_pairI 1),
     (REPEAT (ares_tac [refl] 1))]);

qed_goal "Pow_Union_mono_inj_pair" MonoInj.thy
    "mono_inj_pair(D, Pow, Union)"
  (fn prems =>
    [(rtac mono_inj_pairI 1),
     (rtac Union_Pow_eq 1),
     (rtac Pow_mono 1),
     (rtac Union_mono 2),
     (REPEAT (atac 1))]);

qed_goal "Prod_range_mono_inj_pair" MonoInj.thy
    "b: B ==> mono_inj_pair(D, %X. B * X, range)"
  (fn prems =>
    [(rtac mono_inj_pairI 1),
     (rtac (hd(prems) RS range_of_prod) 1),
     (rtac Sigma_mono 1),
     (rtac range_mono 3),
     (REPEAT (ares_tac [subset_refl] 1))]);

qed_goal "Prod_domain_mono_inj_pair" MonoInj.thy
    "b: B ==> mono_inj_pair(D, %X. X * B, domain)"
  (fn prems =>
    [(rtac mono_inj_pairI 1),
     (rtac (hd(prems) RS domain_of_prod) 1),
     (rtac Sigma_mono 1),
     (rtac domain_mono 3),
     (REPEAT (ares_tac [subset_refl] 1))]);
