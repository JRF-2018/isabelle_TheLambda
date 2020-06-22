(*
    File:        Poset.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open Poset;

fun simp_inst_rule ss insts th =
    let val cth = (read_instantiate insts th) RSN (2, cut_rl);
	val simp_apply = rule_by_tactic (ALLGOALS (asm_full_simp_tac ss))
    in
	hd (Sequence.list_of_s (assumption 1 (simp_apply cth)))
    end;

fun qed_by_simp_inst_rule name ss insts th =
    bind_thm(name, simp_inst_rule ss insts th);

(* poset *)
qed_goalw "posetI" Poset.thy [poset_def]
    "[| !!x. x: P ==> R(x, x); \
\       !!x y. [| x: P; y: P; R(x, y); R(y, x) |] ==> x = y; \
\       !!x y z. [| x: P; y: P; z: P; R(x, y); R(y, z) |] ==> R(x, z) \
\    |] ==> poset(R, P)"
  (fn prems =>
    [(safe_tac ZF_cs),
     (REPEAT (DEPTH_SOLVE_1 ((eresolve_tac prems 1) 
			     THEN (REPEAT (atac 1)))))]);

qed_goalw "poset_reflD" Poset.thy [poset_def]
    "[| poset(R, P); x: P |] ==> R(x, x)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct1 RS bspec) 1),
     (rtac prem 1)]);

qed_goalw "poset_antisymD" Poset.thy [poset_def]
    "[| poset(R, P); R(x, y); R(y, x); x: P; y: P |] ==> x = y"
  (fn major::prems =>
    [(rtac (major RS conjunct2 RS conjunct1 RS bspec RS bspec RS mp) 1),
     (REPEAT (ares_tac ([conjI] @ prems) 1))]);

qed_goalw "poset_transD" Poset.thy [poset_def]
    "[| poset(R, P); R(x, y); R(y, z); x: P; y: P; z: P |] ==> R(x, z)"
  (fn major::prems =>
    [(rtac (major RS conjunct2 RS conjunct2 
	    RS bspec RS bspec RS bspec RS mp) 1),
     (REPEAT (ares_tac ([conjI] @ prems) 4)),
     (REPEAT (ares_tac prems 1))]);

qed_goal "poset_subset" Poset.thy
    "[| S <= P; poset(R, P) |] ==> poset(R, S)"
  (fn [major, prem] =>
    [(rtac posetI 1),
     (REPEAT (ares_tac (([prem] RL [poset_reflD, poset_antisymD, 
				 poset_transD]) @ [major RS subsetD]) 1))]);

qed_goalw "poset_invrel_iff" Poset.thy [poset_def, invrel_def]
    "poset(invrel(R), P) <-> poset(R, P)"
  (fn _ =>
    [(safe_tac ZF_cs),
     (etac (bspec RS bspec RS bspec RS mp) 4),
     (REPEAT (ares_tac [conjI] 7)),
     (etac (bspec RS bspec RS bspec RS mp) 2),
     (REPEAT (ares_tac [conjI] 5)),
     (etac (bspec RS bspec RS mp) 5),
     (etac (bspec RS bspec RS mp) 1),
     (REPEAT (ares_tac [conjI] 1))]);


(** chain **)
qed_goalw "chainI" Poset.thy [chain_def]
    "[| poset(R, P); !!x y. [| x: P; y: P |] ==> R(x, y) | R(y, x) |] \
\        ==> chain(R, P)"
  (fn prems =>
    [(REPEAT (ares_tac ([conjI, ballI] @ prems) 1))]);

qed_goalw "chain_imp_poset" Poset.thy [chain_def]
    "chain(R, P) ==> poset(R, P)"
  (fn [major] =>
    [(rtac (major RS conjunct1) 1)]);

val chainD1 = chain_imp_poset;

qed_goalw "chainD2" Poset.thy [chain_def]
    "[| chain(R, P); x: P; y: P |] ==> R(x, y) | R(y, x)"
  (fn major::prems =>
    [(rtac (major RS conjunct2 RS bspec RS bspec) 1),
     (REPEAT (ares_tac prems 1))]);

qed_goal "chain_subset" Poset.thy
    "[| S <= P; chain(R, P) |] ==> chain(R, S)"
  (fn [major, prem] =>
    [(rtac chainI 1),
     (rtac ([major, prem RS chain_imp_poset] MRS poset_subset) 1),
     (REPEAT (ares_tac [prem RS chainD2, major RS subsetD] 1))]);

qed_goalw "chain_invrel_iff" Poset.thy [chain_def, invrel_def]
    "chain(invrel(R), P) <-> chain(R, P)"
  (fn _ =>
    [(asm_simp_tac (IFOL_ss addsimps [poset_invrel_iff]) 1),
     (fast_tac ZF_cs 1)]);


(** least/greatest **)
qed_goalw "leastI" Poset.thy [least_def]
    "[| !!y. y: P ==> R(x, y); x: P |] ==> least(R, P, x)"
  (fn prems =>
    [(fast_tac (ZF_cs addIs prems) 1)]);

qed_goalw "leastD1" Poset.thy [least_def]
    "least(R, P, x) ==> x: P"
  (fn [prem] =>
    [(rtac (prem RS conjunct1) 1)]);

qed_goalw "leastD2" Poset.thy [least_def]
    "[| least(R, P, x); y: P |] ==> R(x, y)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS bspec) 1),
     (rtac prem 1)]);

qed_goal "least_unique" Poset.thy
    "[| least(R, P, x); least(R, P, y); poset(R, P) |] ==> x = y"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem3 RS poset_antisymD) 1),
     (REPEAT (ares_tac ([prem1, prem2] RL [leastD2, leastD1]) 1))]);

qed_goal "least_subset" Poset.thy
    "[| S <= P; least(R, P, x); x: S |] ==> least(R, S, x)"
  (fn [major, prem1, prem2] =>
    [(rtac leastI 1),
     (rtac prem2 2),
     (etac (major RS subsetD RS (prem1 RS leastD2)) 1)]);

qed_goal "Finite_non_empty_chain_has_least_element" Poset.thy
    "[| Finite(P); chain(R, P); P ~= 0 |] ==> EX x. least(R, P, x)"
  (fn [major, prem1, prem2] =>
    [(rtac (prem2 RS rev_mp) 1),
     (rtac (prem1 RS rev_mp) 1),
     (rtac (major RS Finite_imp_Fin RS Fin_induct) 1),
     (fast_tac ZF_cs 1),
     (REPEAT (rtac impI 1)),
     (excluded_middle_tac "y = 0" 1),
     (hyp_subst_tac 2),
     (rtac exI 2),
     (rtac leastI 2),
     (rtac singletonI 3),
     (etac singletonE 2),
     (hyp_subst_tac 2),
     (etac (chain_imp_poset RS poset_reflD) 2),
     (rtac singletonI 2),
     (dtac (mp RS mp) 1),
     (rtac chain_subset 1),
     (REPEAT (ares_tac [subset_consI] 1)),
     (etac exE 1),
     (forward_tac [chainD2] 1),
     (rtac consI1 1),
     (rtac consI2 1),
     (etac leastD1 1),
     (etac disjE 1),
     (res_inst_tac [("x", "x")] exI 1),
     (res_inst_tac [("x", "xa")] exI 2),
     (ALLGOALS (rtac leastI)),
     (rtac consI2 4),
     (safe_tac ZF_cs),
     (etac (chain_imp_poset RS poset_reflD) 1),
     (etac (chain_imp_poset RS poset_transD) 2),
     (atac 2),
     (rtac consI2 4),
     (etac consI2 5),
     (etac leastD2 2),
     (etac leastD2 5),
     (REPEAT (ares_tac [consI1, leastD1] 1))]);

qed_goalw "least_invrel_iff" Poset.thy [least_def, greatest_def, invrel_def]
    "least(invrel(R), P, x) <-> greatest(R, P, x)"
  (fn _ =>
    [(rtac iff_refl 1)]);

qed_goalw "greatest_invrel_iff" Poset.thy [least_def, greatest_def, invrel_def]
    "greatest(invrel(R), P, x) <-> least(R, P, x)"
  (fn _ =>
    [(rtac iff_refl 1)]);


(** minimal/maximal **)
qed_goalw "minimalI" Poset.thy [minimal_def]
    "[| !!y. [| y: P;  R(y, x) |] ==> y = x; x: P |] ==> minimal(R, P, x)"
  (fn prems =>
    [(fast_tac (ZF_cs addIs prems) 1)]);

qed_goalw "minimalD1" Poset.thy [minimal_def]
    "minimal(R, P, x) ==> x: P"
  (fn [prem] =>
    [(rtac (prem RS conjunct1) 1)]);

qed_goalw "minimalD2" Poset.thy [minimal_def]
    "[| minimal(R, P, x); R(y, x); y: P |] ==> y = x"
  (fn major::prems =>
    [(rtac (major RS conjunct2 RS bspec RS mp) 1),
     (REPEAT (ares_tac prems 1))]);

qed_goal "minimal_subset" Poset.thy
    "[| S <= P; minimal(R, P, x); x: S |] ==> minimal(R, S, x)"
  (fn [major, prem1, prem2] =>
    [(rtac minimalI 1),
     (rtac (prem1 RS minimalD2) 1),
     (REPEAT (ares_tac [prem2, major RS subsetD] 1))]);

qed_goal "least_imp_minimal" Poset.thy
    "[| least(R, P, x); poset(R, P) |] ==> minimal(R, P, x)"
  (fn [major, prem] =>
    [(rtac minimalI 1),
     (rtac (prem RS poset_antisymD) 1),
     (rtac (major RS leastD2) 2),
     (REPEAT (ares_tac [major RS leastD1] 1))]);

qed_goal "chain_minimal_imp_least" Poset.thy
    "[| minimal(R, P, x); chain(R, P) |] ==> least(R, P, x)"
  (fn [major, prem] =>
    [(rtac leastI 1),
     (rtac ([prem, major RS minimalD1] MRS chainD2 RS disjE) 1),
     (atac 1),
     (dtac (major RS minimalD2) 2),
     (hyp_subst_tac 3),
     (REPEAT (ares_tac [major RS minimalD1, 
		      prem RS chain_imp_poset RS poset_reflD] 1))]);

qed_goalw "minimal_invrel_iff" Poset.thy [minimal_def, maximal_def, invrel_def]
    "minimal(invrel(R), P, x) <-> maximal(R, P, x)"
  (fn _ =>
    [(rtac iff_refl 1)]);

qed_goalw "maximal_invrel_iff" Poset.thy [minimal_def, maximal_def, invrel_def]
    "maximal(invrel(R), P, x) <-> minimal(R, P, x)"
  (fn _ =>
    [(rtac iff_refl 1)]);


(** upset/downset **)
qed_goalw "upsetI" Poset.thy [upset_def]
    "[| y: P; R(x, y) |] ==> y: upset(R, P, x)"
  (fn prems =>
    [(REPEAT (ares_tac ([CollectI] @ prems) 1))]);

qed_goalw "upsetE" Poset.thy [upset_def]
    "[| y: upset(R, P, x); [| y: P; R(x, y) |] ==> Q |] ==> Q"
  (fn [major, prem] =>
    [(rtac (major RS CollectE) 1),
     (REPEAT (ares_tac [prem] 1))]);

qed_goal "least_upset" Poset.thy
    "[| poset(R, P); x: P |] ==> least(R, upset(R, P, x), x)"
  (fn [prem1, prem2] =>
    [(rtac leastI 1),
     (etac upsetE 1),
     (REPEAT (ares_tac [prem2, upsetI, prem1 RS poset_reflD] 1))]);

qed_goal "upset_subset" Poset.thy
    "upset(R, P, x) <= P"
  (fn _ =>
    [(fast_tac (ZF_cs addSEs [upsetE]) 1)]);

qed_goalw "upset_invrel_eq" Poset.thy [downset_def, upset_def, invrel_def]
    "upset(invrel(R), P, x) = downset(R, P, x)"
  (fn _ =>
    [(rtac refl 1)]);

qed_goalw "downset_invrel_eq" Poset.thy [downset_def, upset_def, invrel_def]
    "downset(invrel(R), P, x) = upset(R, P, x)"
  (fn _ =>
    [(rtac refl 1)]);

(** upperbound/lowerbound **)
qed_goalw "upperboundI" Poset.thy [upperbound_def]
    "[| x: P; !!y. y: S ==> R(y, x) |] ==> x: upperbound(R, P, S)"
  (fn [prem1, prem2] =>
    [(fast_tac (ZF_cs addIs [prem1, prem2]) 1)]);

qed_goalw "upperboundE" Poset.thy [upperbound_def]
    "[| x: upperbound(R, P, S); [| x: P; ALL y: S. R(y, x) |] ==> Q |] ==> Q"
  (fn [major, prem] =>
    [(rtac (major RS CollectE) 1),
     (REPEAT (ares_tac [prem] 1))]);

qed_goalw "upperbound_invrel_eq" Poset.thy [lowerbound_def, upperbound_def, 
					    invrel_def]
    "upperbound(invrel(R), P, S) = lowerbound(R, P, S)"
  (fn _ =>
    [(rtac refl 1)]);

qed_goalw "lowerbound_invrel_eq" Poset.thy [lowerbound_def, upperbound_def, 
					    invrel_def]
    "lowerbound(invrel(R), P, S) = upperbound(R, P, S)"
  (fn _ =>
    [(rtac refl 1)]);


(** Prove symmetric theorems **)

val Poset_symmetric_ss = IFOL_ss addsimps 
    [least_invrel_iff, greatest_invrel_iff,
     minimal_invrel_iff, maximal_invrel_iff,
     downset_invrel_eq, upset_invrel_eq,
     lowerbound_invrel_eq, upperbound_invrel_eq,
     chain_invrel_iff, poset_invrel_iff, invrel_def];

val _ = map (fn (name, th) => qed_by_simp_inst_rule name Poset_symmetric_ss 
	     [("R", "invrel(R)")] th)
    [("greatestI", leastI),
     ("greatestD1", leastD1),
     ("greatestD2", leastD2),
     ("greatest_unique", least_unique),
     ("greatest_subset", least_subset),
     ("Finite_non_empty_chain_has_greatest_element",
      Finite_non_empty_chain_has_least_element),
     ("maximalI", minimalI),
     ("maximalD1", minimalD1),
     ("maximalD2", minimalD2),
     ("maximal_subset", minimal_subset),
     ("greatest_imp_maximal", least_imp_minimal),
     ("chain_maximal_imp_greatest", chain_minimal_imp_least),
     ("downsetI", upsetI),
     ("downsetE", upsetE),
     ("downset_subset", upset_subset),
     ("greatest_downset", least_upset),
     ("lowerboundI", upperboundI),
     ("lowerboundE", upperboundE)];
