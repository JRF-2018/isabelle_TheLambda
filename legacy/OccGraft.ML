(*
    File:        OccGraft.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open OccGraft;

(** lists_subtree **)
qed_goalw "lists_subtreeI" OccGraft.thy [lists_subtree_def]
    "Cons(b, l): X ==> l: lists_subtree(b, X)"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac (ZF_cs addSEs list.free_SEs) 1)]);

qed_goalw "lists_subtreeD" OccGraft.thy [lists_subtree_def]
    "l: lists_subtree(b, X) ==> Cons(b, l): X"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac ZF_cs 1)]);

val lists_subtreeE = standard(make_elim(lists_subtreeD));

qed_goal "lists_subtree_domain_eq" OccGraft.thy
    "lists_subtree(b, domain(X)) = domain(Occ_subtree(b, X))"
  (fn _ =>
    [(fast_tac (eq_cs addIs [Occ_subtreeI, lists_subtreeI]
		addSEs [Occ_subtreeE, lists_subtreeE]) 1)]);

qed_goal "lists_subtree_mono" OccGraft.thy
    "X <= W ==> lists_subtree(b, X) <= lists_subtree(b, W)"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac (ZF_cs addSEs [lists_subtreeE] addIs [lists_subtreeI]) 1)]);

(** Occ_Shift **)
qed_goalw "Occ_ShiftI" OccGraft.thy [Occ_Shift_def]
    "<l, T>: X ==> <m@l, T>: Occ_Shift(m, X)"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (rtac ReplaceI 1),
     (rtac prem 2),
     (REPEAT (resolve_tac [refl, conjI, exI] 1)),
     (REPEAT (eresolve_tac [exE, conjE] 1)),
     (asm_full_simp_tac (IFOL_ss addsimps [Pair_iff]) 1)]);

qed_goalw "Occ_ShiftD" OccGraft.thy [Occ_Shift_def]
    "[| <m@l, T>: Occ_Shift(m, X); m: list(A) |] ==> <l, T>: X"
  (fn [prem, m_list] =>
    [(cut_facts_tac [prem, m_list] 1),
     (REPEAT (eresolve_tac [ReplaceE, exE, conjE] 1)),
     (asm_full_simp_tac (IFOL_ss addsimps [Pair_iff, app_right_inj_iff]) 1),
     (hyp_subst_tac 1),
     (atac 1)]);

qed_goalw "Occ_ShiftE" OccGraft.thy [Occ_Shift_def]
    "[| x: Occ_Shift(m, X); \
\       !!l T. [| x = <m@l, T>; <l, T>: X |] ==> R \
\     |]==> R"
  (fn [major, prem] =>
    [(rtac (major RS ReplaceE) 1),
     (REPEAT (eresolve_tac [conjE, exE] 1)),
     (rtac prem 1),
     (atac 1),
     (dtac spec 1),
     (dtac mp 1),
     (REPEAT (ares_tac [exI, conjI] 1)),
     (hyp_subst_tac 1),
     (atac 1)]);

qed_goal "Occ_ShiftE2" OccGraft.thy
    "[| <n, T>: Occ_Shift(m, X); \
\       !!l. [| n = m@l; <l, T>: X |] ==> R \
\     |]==> R"
  (fn [major, prem] =>
    [(rtac (major RS Occ_ShiftE) 1),
     (rtac prem 1),
     (ALLGOALS (asm_full_simp_tac (IFOL_ss addsimps [Pair_iff])))]);

qed_goalw "Occ_Shift_0" OccGraft.thy [Occ_Shift_def]
    "Occ_Shift(m, 0) = 0"
  (fn _ =>
    [(fast_tac eq_cs 1)]);

qed_goalw "Occ_Shift_Nil" OccGraft.thy [Occ_Shift_def]
    "X <= A * B ==> Occ_Shift([], X) = X"
  (fn [prem] =>
    [(simp_tac list_ss 1),
     (cut_facts_tac [prem] 1),
     (fast_tac eq_cs 1)]);

qed_goal "Occ_Shift_Cons" OccGraft.thy
    "Occ_Shift(Cons(a, l), X) = Occ_shift(a, Occ_Shift(l, X))"
  (fn _ =>
    [(rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [Occ_shiftE, Occ_ShiftE])),
     (simp_tac list_ss 1),
     (fast_tac (ZF_cs addIs [Occ_shiftI, Occ_ShiftI]) 1),
     (simp_tac (list_ss delsimps [app_Cons] addsimps [app_Cons RS sym]) 1),
     (rtac Occ_ShiftI 1),
     (atac 1)]);

qed_goal "Occ_Shift_domain" OccGraft.thy
    "[| X <= list(A) * B; m: list(A) |] ==> Occ_Shift(m, X) <= list(A) * B"
  (fn [prem1, prem2] =>
    [(cut_facts_tac [prem1, prem2] 1),
     (fast_tac (ZF_cs addIs [app_type] addSEs [Occ_ShiftE]) 1)]);

qed_goal "Occ_Shift_app" OccGraft.thy
    "[| l: list(A); m: list(B); X <= list(B) * D |] ==> \
\         Occ_Shift(l@m, X) = Occ_Shift(l, Occ_Shift(m, X))"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem3 RS rev_mp) 1),
     (res_inst_tac [("x", "X")] spec 1),
     (list_ind_tac "l" [prem1] 1),
     (rtac (impI RS allI) 1),
     (dtac Occ_Shift_domain 1),
     (rtac prem2 1),
     (ALLGOALS (asm_simp_tac (list_ss addsimps [Occ_Shift_Nil,
						Occ_Shift_Cons])))]);


(** Incomparable **)
qed_goalw "IncomparableI" OccGraft.thy [Incomparable_def]
    "[| !!l m. [| l: W; m: W; initseg(nat, l, m) |] ==> l = m |]\
\      ==> Incomparable(W)"
  (fn [prem1] =>
    [(REPEAT (resolve_tac [ballI, impI] 1)),
     (etac disjE 1),
     (rtac (prem1 RS sym) 2),
     (rtac prem1 1),
     (REPEAT (atac 1))]);

qed_goalw "IncomparableD" OccGraft.thy [Incomparable_def]
    "[| Incomparable(W); \
\       initseg(nat, l, m); \
\       l: W; m: W |] ==> l = m"
  (fn major::prems =>
    [(rtac (major RS bspec RS bspec RS mp) 1),
     (rtac disjI1 3),
     (REPEAT (ares_tac prems 1))]);

qed_goal "Incomparable_lists_subtree" OccGraft.thy
    "[| Incomparable(W); a: nat |] ==> Incomparable(lists_subtree(a, W))"
  (fn [major, prem] =>
    [(rtac IncomparableI 1),
     (REPEAT (etac lists_subtreeE 1)),
     (dtac (prem RS initseg_ConsI) 1),
     (dtac (major RS IncomparableD) 1),
     (REPEAT (atac 1)),
     (asm_full_simp_tac (list_ss addsimps [Cons_iff]) 1)]);

qed_goal "Incomparable_subset" OccGraft.thy
    "[| Incomparable(W); X <= W |] ==> Incomparable(X)"
  (fn [major, prem] =>
    [(rtac IncomparableI 1),
     (etac (major RS IncomparableD) 1),
     (REPEAT (etac (prem RS subsetD) 1))]);

qed_goal "Incomparable_CorrectArity_0_lemma" OccGraft.thy
    "[| initseg(nat, l, m); <l, T>: X; <m, U>: X; DenseTree(X);\
\       CorrectArity(X, T, 0); m: list(nat) \
\    |] ==> l = m"
  (fn [major, prem1, prem2, hierX, corrT, m_list] =>
    [(rtac (prem2 RS rev_mp) 1),
     (rtac (prem1 RS rev_mp) 1),
     (rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "U")] spec 1),
     (rtac (m_list RS list_append_induct) 1),
     (ALLGOALS (REPEAT o (resolve_tac [impI, allI]))),
     (etac initseg_NilE 1),
     (atac 1),
     (etac initseg_right_appE 1),
     (atac 1),
     (rtac (corrT RS CorrectArityD2 RS notE) 1),
     (atac 1),
     (etac (nat_into_Ord RS Ord_0_le) 1),
     (rtac (hierX RS DenseTreeE) 1),
     (rtac initseg_appI1 2),
     (REPEAT (atac 1)),
     (dtac spec 1),
     (REPEAT (mp_tac 1)),
     (hyp_subst_tac 1),
     (etac exI 1),
     (eres_inst_tac [("a", "xb")] list.elim 1),
     (REPEAT (hyp_subst_tac 1)),
     (asm_full_simp_tac (IFOL_ss addsimps [app_right_Nil, app_Nil]) 1),
     (rtac (corrT RS CorrectArityD2 RS notE) 1),
     (etac exI 3),
     (etac (nat_into_Ord RS Ord_0_le) 2),
     (atac 1),
     (REPEAT (hyp_subst_tac 1)),
     (asm_full_simp_tac (IFOL_ss addsimps [app_Cons, Cons_iff]) 1),
     (etac conjE 1),
     (etac (sym RS app_eq_NilD RS conjE) 1),
     (atac 1),
     (asm_simp_tac list_ss 1)]);

qed_goal "Incomparable_CorrectArity_0" OccGraft.thy
    "[| X <= list(nat)* B; DenseTree(X) |] \
\     ==> Incomparable(domain({<l, T>: X. CorrectArity(X, T, 0)}))"
  (fn [domX, hierX] =>
    [(rtac IncomparableI 1),
     (REPEAT (eresolve_tac [domainE, CollectE] 1)),
     (asm_full_simp_tac ZF_ss 1),
     (etac Incomparable_CorrectArity_0_lemma 1),
     (etac (domX RS subsetD RS SigmaD1) 5),
     (REPEAT (ares_tac [hierX] 1))]);

(** Occ_Graft1 **)
qed_goalw "Occ_Graft1I1" OccGraft.thy [Occ_Graft1_def]
    "[| <l, T>: X; ~initseg(nat, m, l) |] \
\       ==> <l, T>: Occ_Graft1(X, m, Y)"
  (fn [prem1, prem2] =>
    [(rtac UnI1 1),
     (rtac DiffI 1),
     (rtac prem1 1),
     (rtac notI 1),
     (rtac (prem2 RS notE) 1),
     (REPEAT (eresolve_tac [CollectE, exE, conjE] 1)),
     (asm_full_simp_tac ZF_ss 1)]);

qed_goalw "Occ_Graft1I2" OccGraft.thy [Occ_Graft1_def]
    "<l, T>: Occ_Shift(m, Y) ==> <l, T>: Occ_Graft1(X, m, Y)"
  (fn [prem] =>
    [(rtac UnI2 1),
     (REPEAT (ares_tac [prem] 1))]);

qed_goalw "Occ_Graft1E" OccGraft.thy [Occ_Graft1_def]
    "[| x: Occ_Graft1(X, m, Y); \
\       X <= A * B; \
\       !! l T. [| x = <l, T>; <l, T>: X; l: A; T: B; \
\                 ~initseg(nat, m, l) |] ==> R; \
\       x: Occ_Shift(m, Y) ==> R \
\    |] ==> R"
  (fn [major, prem, prem1, prem2] =>
    [(rtac (major RS UnE) 1),
     (etac prem2 2),
     (etac DiffE 1),
     (forward_tac [prem RS subsetD] 1),
     (etac SigmaE 1),
     (rtac prem1 1),
     (hyp_subst_tac 2),
     (rtac notI 5),
     (etac notE 5),
     (REPEAT (ares_tac [CollectI, exI, conjI] 1))]);

qed_goal "Occ_Graft1_domain" OccGraft.thy
    "[| X <= list(A) * B; Y <= list(A) * B; m: list(A) |] \
\         ==> Occ_Graft1(X, m, Y) <= list(A) * B"
  (fn [domX, domY, m_list] =>
    [(rtac subsetI 1),
     (etac Occ_Graft1E 1),
     (rtac domX 1),
     (etac ([domY, m_list] MRS Occ_Shift_domain RS subsetD) 2),
     (fast_tac ZF_cs 1)]);

qed_goal "Occ_Graft1_Nil" OccGraft.thy
    "[| X <= list(nat) * B; Y <= list(nat) * D |] ==> \
\          Occ_Graft1(X, [], Y) = Y"
  (fn [prem1, prem2] =>
    [(rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [prem1 RSN (2, Occ_Graft1E), Occ_ShiftE])),
     (asm_simp_tac list_ss 2),
     (etac notE 1),
     (etac initseg_NilI 1),
     (forward_tac [prem2 RS subsetD] 1),
     (etac SigmaE 1),
     (hyp_subst_tac 1),
     (rtac Occ_Graft1I2 1),
     (res_inst_tac [("P", "%x. <x, ?X>: ?Y")] (app_Nil RS subst) 1),
     (etac Occ_ShiftI 1)]);

qed_goal "Occ_Graft1_Occ_cons_Cons" OccGraft.thy
    "[| T: Tag; l: list(Pow(list(nat)*Tag)); m: list(nat); \
\       a: length(l) |] ==> \
\     Occ_Graft1(Occ_cons(T, l), Cons(a, m), Y) = \
\         Occ_cons(T, mapnth(%x r. if(a = x, Occ_Graft1(r, m, Y), r), l))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [Occ_cons_type RSN (2, Occ_Graft1E),
			    Occ_ShiftE, Occ_consE])),
     (TRYALL (ares_tac [Occ_consI1])),
     (asm_simp_tac nth_ss 2),
     (rtac Occ_Graft1I1 3),
     (rtac Occ_consI1 3),
     (fast_tac (ZF_cs addSEs list.free_SEs addSEs [initseg_NilE]) 3),
     (rtac Occ_consI2 2),
     (rtac Occ_consI2 1),
     (excluded_middle_tac "a = aa" 5),
     (rotate_tac 6 5),
     (rotate_tac 6 6),
     (excluded_middle_tac "a = aa" 2),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps 
				 [nth_mapnth, length_mapnth]))),
     (safe_tac (ZF_cs addSEs [Occ_Graft1E, Occ_ShiftE])),
     (dtac nth_type2 4),
     (etac (PowD RS subsetD) 5),
     (REPEAT (ares_tac ([length_type, nat_ltI] @ prems) 4)),
     (rtac Occ_Graft1I2 5),
     (asm_simp_tac (IFOL_ss addsimps [app_Cons RS sym]) 5),
     (etac Occ_ShiftI 5),
     (rtac Occ_Graft1I1 4),
     (REPEAT (ares_tac [Occ_consI2] 4)),
     (fast_tac (ZF_cs addSEs [initseg_left_ConsE] addSEs list.free_SEs) 4),
    (* 25 *)
     (rtac Occ_Graft1I1 3),
     (REPEAT (ares_tac [Occ_consI2] 3)),
     (fast_tac (ZF_cs addSEs [initseg_left_ConsE] addSEs list.free_SEs) 3),
     (rtac Occ_Graft1I2 2),
     (etac Occ_ShiftI 2),
     (rtac Occ_Graft1I1 1),
     (atac 1),
     (dtac (length_type RSN (2, mem_nat_in_nat)) 1),
     (atac 1),
     (fast_tac (ZF_cs addIs [initseg_ConsI]) 1)]);


(** Occ_Graft **)
qed_goalw "Occ_GraftI1" OccGraft.thy [Occ_Graft_def]
    "[| <l, T>: X; ~(EX m: W. initseg(nat, m, l)) |] \
\       ==> <l, T>: Occ_Graft(X, W, Y)"
  (fn [prem1, prem2] =>
    [(rtac UnI1 1),
     (rtac DiffI 1),
     (rtac prem1 1),
     (rtac notI 1),
     (rtac (prem2 RS notE) 1),
     (REPEAT (eresolve_tac [UN_E, CollectE, exE, conjE] 1)),
     (rtac bexI 1),
     (atac 2),
     (asm_full_simp_tac ZF_ss 1)]);

qed_goalw "Occ_GraftI2" OccGraft.thy [Occ_Graft_def]
    "[| m: W; <l, T>: Occ_Shift(m, Y) |] \
\            ==> <l, T>: Occ_Graft(X, W, Y)"
  (fn [prem1, prem2] =>
    [(rtac UnI2 1),
     (rtac UN_I 1),
     (REPEAT (ares_tac [prem1, prem2] 1))]);

qed_goalw "Occ_GraftE" OccGraft.thy [Occ_Graft_def]
    "[| x: Occ_Graft(X, W, Y); \
\       X <= A * B; \
\       !! l T. [| x = <l, T>; <l, T>: X; l: A; T: B; \
\                 ~(EX m: W. initseg(nat, m, l)) |] ==> R; \
\       !! m. [| m: W; x: Occ_Shift(m, Y) |] ==> R \
\    |] ==> R"
  (fn [major, prem, prem1, prem2] =>
    [(rtac (major RS UnE) 1),
     (etac UN_E 2),
     (rtac prem2 2),
     (etac DiffE 1),
     (forward_tac [prem RS subsetD] 1),
     (etac SigmaE 1),
     (rtac prem1 1),
     (hyp_subst_tac 2),
     (rtac notI 5),
     (etac notE 5),
     (etac bexE 5),
     (REPEAT (ares_tac [UN_I, CollectI, exI, conjI] 1))]);

qed_goal "Occ_Graft_domain" OccGraft.thy
    "[| X <= list(A) * B; Y <= list(A) * B; W <= domain(X) |] \
\         ==> Occ_Graft(X, W, Y) <= list(A) * B"
  (fn [domX, domY, domW] =>
    [(rtac subsetI 1),
     (etac Occ_GraftE 1),
     (rtac domX 1),
     (rtac (domY RS Occ_Shift_domain RS subsetD) 2),
     (dtac (domW RS subsetD) 2),
     (etac domainE 2),
     (dtac (domX RS subsetD) 2),
     (etac SigmaD1 2),
     (fast_tac ZF_cs 1),
     (atac 1)]);

qed_goalw "Occ_Graft_0" OccGraft.thy [Occ_Graft_def]
    "Occ_Graft(X, 0, Y) = X"
  (fn _ =>
    [(simp_tac ZF_ss 1)]);

qed_goal "Occ_Graft_cons" OccGraft.thy
    "[| Incomparable(cons(a, W)); cons(a, W) <= domain(X); \
\      X <= list(nat) * Tag; Y <= list(nat) * Tag\
\    |] ==> Occ_Graft(X, cons(a, W), Y) = \
\                Occ_Graft1(Occ_Graft(X, W - {a}, Y), a, Y)"
  (fn [prem, domW, domX, domY] =>
    [(rtac equalityI 1),
     (ALLGOALS (rtac subsetI)),
     (etac Occ_GraftE 1),
     (rtac domX 1),
     (etac Occ_ShiftE 2),
     (etac Occ_Graft1E 3),
     (rtac Occ_Graft_domain 3),
     (rtac (domW RSN (2, subset_trans)) 5),
     (fast_tac ZF_cs 5),
     (REPEAT (ares_tac [domX, domY] 3)),
     (etac Occ_GraftE 3),
     (rtac domX 3),
     (etac Occ_ShiftE 5),
     (etac Occ_ShiftE2 4),
     (ALLGOALS hyp_subst_tac),
     (rtac Occ_GraftI2 5),
     (rtac Occ_GraftI2 4),
     (TRYALL (rtac Occ_ShiftI)),
     (fast_tac ZF_cs 4),
     (REPEAT (ares_tac [consI1] 4)),
     (rtac Occ_GraftI1 3),
     (rtac notI 4),
     (fast_tac ZF_cs 4),
     (asm_full_simp_tac nth_ss 3),
     (res_inst_tac [("Q", "m = a")] (excluded_middle RS disjE) 2),
     (hyp_subst_tac 3),
     (rtac Occ_Graft1I2 3),
     (etac Occ_ShiftI 3),
     (ALLGOALS (rtac Occ_Graft1I1)),
     (rtac Occ_GraftI1 1),
     (atac 1),
     (fast_tac ZF_cs 1),
     (fast_tac ZF_cs 1),
     (rtac Occ_GraftI2 1),
     (etac Occ_ShiftI 2),
     (fast_tac ZF_cs 1),
     (rtac notI 1),
     (etac notE 1),
     (etac initseg_right_appE 1),
     (dtac (domW RS subsetD) 1),
     (etac domainE 1),
     (etac (domX RS subsetD RS SigmaD1) 1),
     (ALLGOALS (dtac (prem RS IncomparableD))),
     (REPEAT (ares_tac [consI1, sym] 1))]);

qed_goal "Occ_Graft_cons2" OccGraft.thy
    "[| Incomparable(cons(a, W)); cons(a, W) <= domain(X); \
\      X <= list(nat) * Tag; Y <= list(nat) * Tag\
\    |] ==> Occ_Graft(X, cons(a, W), Y) = \
\                Occ_Graft(Occ_Graft1(X, a, Y), W - {a}, Y)"
  (fn [prem, domW, domX, domY] =>
    [(rtac equalityI 1),
     (ALLGOALS (rtac subsetI)),
     (etac Occ_GraftE 1),
     (rtac domX 1),
     (etac Occ_ShiftE 2),
     (etac Occ_GraftE 3),
     (rtac Occ_Graft1_domain 3),
     (cut_facts_tac [consI1 RS (domW RS subsetD)] 5),
     (etac domainE 5),
     (etac (domX RS subsetD RS SigmaD1) 5),
     (REPEAT (ares_tac [domX, domY] 3)),
     (etac Occ_Graft1E 3),
     (rtac domX 3),
     (etac Occ_ShiftE 5),
     (etac Occ_ShiftE2 4),
     (ALLGOALS hyp_subst_tac),
     (rtac Occ_GraftI2 5),
     (rtac Occ_GraftI2 4),
     (res_inst_tac [("Q", "m = a")] (excluded_middle RS disjE) 2),
     (rtac Occ_GraftI2 2),
     (TRYALL (rtac Occ_ShiftI)),
     (etac consE 2),
     (etac notE 2),
     (rtac DiffI 3),
     (rtac notI 4),
     (etac singletonE 4),
     (etac notE 4),
     (etac DiffE 10),
     (TRYALL (REPEAT o (ares_tac [consI1, consI2]))),
     (hyp_subst_tac 2),
     (ALLGOALS (rtac Occ_GraftI1)),
     (TRYALL ((rtac notI) THEN' (etac notE))),
     (TRYALL (etac bexE)),
     (res_inst_tac [("Q", "m = a")] (excluded_middle RS disjE) 6),
     (hyp_subst_tac 7),
     (etac notE 7),
     (asm_full_simp_tac nth_ss 7),
     (fast_tac ZF_cs 2),
     (asm_full_simp_tac nth_ss 4),
     (fast_tac ZF_cs 4),
     (rtac notI 3),
     (etac bexE 3),
     (rtac Occ_Graft1I2 2),
     (rtac Occ_ShiftI 2),
     (rtac Occ_Graft1I1 1),
     (rtac notI 2),
     (etac notE 2),
     (fast_tac ZF_cs 2),
     (TRYALL atac),
     (etac initseg_right_appE 1),
     (cut_facts_tac [consI1 RS (domW RS subsetD)] 1),
     (etac domainE 1),
     (etac (domX RS subsetD RS SigmaD1) 1),
     (ALLGOALS (dtac (prem RS IncomparableD))),
     (dres_inst_tac [("a", "a")] sym 6),
     (ALLGOALS (fast_tac ZF_cs))]);

qed_goalw "Occ_Graft_Nil" OccGraft.thy [Occ_Graft_def]
    "[| X <= list(nat) * Tag; Y <= A * B |] ==> \
\       Occ_Graft(X, {[]}, Y) = Y"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac ZF_cs),
     (TRYALL (etac notE)),
     (TRYALL (rtac (singletonI RS UN_I))),
     (rtac CollectI 1),
     (atac 1),
     (fast_tac (ZF_cs addIs [initseg_NilI]) 1),
     (ALLGOALS (asm_full_simp_tac (IFOL_ss addsimps [Occ_Shift_Nil])))]);

qed_goal "Incomparable_Nil_lemma" OccGraft.thy
    "[| Incomparable(W); []: W; W <= list(nat) |] ==> W = {[]}"
  (fn [major, prem, domW] =>
    [(rtac equalityI 1),
     (cut_facts_tac [prem] 2),
     (fast_tac ZF_cs 2),
     (rtac subsetI 1),
     (res_inst_tac [("P", "%x. x: ?X")] 
    (major RS (prem RSN (3, IncomparableD)) RS subst) 1),
     (dtac (domW RS subsetD) 1),
     (REPEAT (ares_tac [initseg_NilI, singletonI] 1))]);

qed_goal "Occ_Graft_Occ_cons" OccGraft.thy
    "[| W ~= {[]}; Incomparable(W); W <= domain(Occ_cons(T, l)); \
\        T: Tag; l: list(Pow(list(nat)*Tag)); Y <= list(nat) * Tag\
\     |] ==> Occ_Graft(Occ_cons(T, l), W, Y) = \
\         Occ_cons(T, mapnth(%z r. Occ_Graft(r, lists_subtree(z, W), Y), l))"
  (fn [major, prem, domW, t_tag, l_list, domY] =>
    [(cut_facts_tac [t_tag, l_list] 1),
     (subgoals_tac ["W <= list(nat)"] 1),
     (cut_facts_tac [[t_tag, l_list] MRS Occ_cons_type, domW] 2),
     (fast_tac ZF_cs 2),
     (rtac equalityI 1),
     (ALLGOALS (rtac subsetI)),
     (etac Occ_GraftE 1),
     (rtac ([t_tag, l_list] MRS Occ_cons_type) 1),
     (etac Occ_consE 3),
     (etac Occ_ShiftE 2),
     (ALLGOALS hyp_subst_tac),
     (etac Occ_consE 1),
     (safe_tac ZF_cs),
     (forward_tac [domW RS subsetD] 3),
     (safe_tac (ZF_cs addSEs [Occ_consE])),
     (etac (prem RS Incomparable_Nil_lemma RS (major RS notE)) 3),
     (atac 3),
     (asm_simp_tac nth_ss 3),
     (TRYALL (resolve_tac [Occ_consI1, Occ_consI2])),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps [nth_mapnth,
						  length_mapnth]))),
     (rtac Occ_GraftI2 2),
     (etac Occ_ShiftI 3),
     (etac lists_subtreeI 2),
     (rtac Occ_GraftI1 1),
     (rtac notI 2),
     (etac notE 2),
     (forward_tac [length_type RSN (2, mem_nat_in_nat)] 2),
     (atac 2),
     (fast_tac (ZF_cs addSEs [lists_subtreeE] addIs [initseg_ConsI]) 2),
     (atac 1),
     (rtac Occ_GraftI1 1),
     (rtac Occ_consI1 1),
     (rtac notI 1),
     (etac bexE 1),
     (etac initseg_NilE 1),
     (hyp_subst_tac 1),
     (etac (prem RS Incomparable_Nil_lemma RS (major RS notE)) 1),
     (atac 1),
     (etac Occ_GraftE 1),
     (etac (nth_type2 RS PowD) 1),
     (REPEAT (ares_tac [nat_ltI, l_list, length_type] 1)),
     (safe_tac (ZF_cs addSEs [Occ_ShiftE, lists_subtreeE])),
     (asm_simp_tac (IFOL_ss addsimps [app_Cons RS sym]) 2),
     (rtac Occ_GraftI2 2),
     (rtac Occ_ShiftI 3),
     (REPEAT (atac 2)),
     (rtac Occ_GraftI1 1),
     (etac Occ_consI2 1),
     (asm_simp_tac nth_ss 1),
     (forward_tac [length_type RSN (2, mem_nat_in_nat)] 1),
     (atac 1),
     (rtac notI 1),
     (etac notE 1),
     (etac bexE 1),
     (etac initseg_ConsE 1),
     (ALLGOALS hyp_subst_tac),
     (etac (prem RS Incomparable_Nil_lemma RS (major RS notE)) 1),
     (atac 1),
     (fast_tac (ZF_cs addIs [lists_subtreeI]) 1)]);

(** Occ_Graft1 in Occ_range **)
qed_goal "Occ_Graft1_preserves_functionality" OccGraft.thy
    "[| functional(X); functional(Y); X <= list(nat)*B; l: list(nat) |] \
\          ==> functional(Occ_Graft1(X, l, Y))"
  (fn [funcX, funcY, domX, l_list] =>
    [(rtac functionalI 1),
     (etac Occ_Graft1E 1),
     (rtac domX 1),
     (ALLGOALS ((etac Occ_Graft1E) THEN' (rtac domX))),
     (TRYALL (REPEAT o (etac Occ_ShiftE))),
     (ALLGOALS (REPEAT o (etac (Pair_iff RS iffD1 RS conjE)))),
     (ALLGOALS hyp_subst_tac),
     (dtac (l_list RS app_right_inj_iff RS iffD1) 4),
     (hyp_subst_tac 4),
     (etac (funcX RS functionalD) 1),
     (atac 1),
     (etac (funcY RS functionalD) 3),
     (atac 3),
     (ALLGOALS ((etac notE) THEN'
	      (dtac (l_list RSN (2, app_typeD))) THEN'
	      (etac (l_list RS initseg_appI1))))]);

qed_goal "Occ_Graft1_preserves_DenseTree" OccGraft.thy
    "[| DenseTree(X); DenseTree(Y); X <= list(nat)*B; l: domain(X) |] \
\          ==> DenseTree(Occ_Graft1(X, l, Y))"
  (fn [hierX, hierY, domX, l_list] =>
    [(rtac DenseTreeI 1),
     (etac Occ_Graft1E 1),
     (rtac domX 1),
     (etac Occ_ShiftE 2),
     (ALLGOALS (etac (Pair_iff RS iffD1 RS conjE))),
     (ALLGOALS hyp_subst_tac),
     (rtac (hierX RS DenseTreeE) 1),
     (REPEAT (atac 1)),
     (rtac exI 1),
     (etac Occ_Graft1I1 1),
     (rtac notI 1),
     (etac notE 1),
     (etac initseg_trans 1),
     (atac 1),
     (rtac (l_list RS domainE) 1),
     (etac initseg_right_appE 1),
     (etac (domX RS subsetD RS SigmaD1) 1),
     (rtac (hierX RS DenseTreeE) 1),
     (REPEAT (atac 1)),
     (res_inst_tac [("Q", "m = l")] (excluded_middle RS disjE) 1),
     (rtac exI 1),
     (rtac Occ_Graft1I1 1),
     (atac 1),
     (rtac notI 1),
     (dtac (initseg_antisym) 1),
     (atac 1),
     (etac notE 1),
     (atac 1),
     (ALLGOALS hyp_subst_tac),
     (ALLGOALS (etac (hierY RS DenseTreeE))),
     (etac initseg_NilI 1),
     (etac initseg_appI1 2),
     (atac 2),
     (ALLGOALS (rtac exI)),
     (res_inst_tac [("P", "%x. <x, ?X>: ?Y")] (app_right_Nil RS subst) 1),
     (etac (domX RS subsetD RS SigmaD1) 1),
     (ALLGOALS (etac (Occ_ShiftI RS Occ_Graft1I2)))]);

qed_goal "Occ_Graft1_preserves_CorrectArity" OccGraft.thy
    "[| CorrectArity(X, T, n); CorrectArity(Y, T, n); \
\       X <= list(nat)*B; l: domain(X); \
\       Y <= list(nat)*B; DenseTree(Y); Y ~= 0 \
\    |] ==> CorrectArity(Occ_Graft1(X, l, Y), T, n)"
  (fn [corrX, corrY, domX, l_list, domY, hierY, not_emptyY] =>
    [(subgoals_tac ["l: list(nat)"] 1),
     (rtac (l_list RS domainE) 2),
     (etac (domX RS subsetD RS SigmaD1) 2),
     (rtac CorrectArityI 1),
     (ALLGOALS ((etac Occ_Graft1E) THEN' (rtac domX))),
     (res_inst_tac [("Q", "la @ [m] = l")] (excluded_middle RS disjE) 1),
     (TRYALL (etac Occ_ShiftE)),
     (etac (Pair_iff RS iffD1 RS conjE) 5),
     (hyp_subst_tac 5),
     (forward_tac [corrY RS CorrectArityD2] 5),
     (atac 5),
     (etac notE 5),
     (etac exE 5),
     (etac Occ_Graft1E 5),
     (rtac domX 5),
     (etac (Pair_iff RS iffD1 RS conjE) 5),
     (hyp_subst_tac 5),
     (etac notE 5),
     (asm_full_simp_tac (IFOL_ss addsimps [app_assoc]) 5),
     (rtac initseg_appI1 5),
     (atac 5),
     (etac app_typeD 5),
     (atac 5),
     (etac Occ_ShiftE2 5),
     (asm_full_simp_tac (IFOL_ss addsimps [app_assoc, app_right_inj_iff]) 5),
     (etac exI 5),
    (**)
     (etac (Pair_iff RS iffD1 RS conjE) 4),
     (hyp_subst_tac 4),
     (etac exE 4),
     (etac Occ_Graft1E 4),
     (rtac domX 4),
     (etac Occ_ShiftE2 5),
     (rtac (app_appE_lemma RS bspec RS mp RS disjE) 5),
     (atac 7),
     (REPEAT (atac 5)),
     (rtac (l_list RS domainE) 5),
     (etac exE 5),
     (hyp_subst_tac 5),
     (asm_full_simp_tac (IFOL_ss addsimps [app_assoc, app_right_inj_iff]) 5),
     (dtac app_typeD 5),
     (atac 5),
     (eres_inst_tac [("a", "z")] list.elim 5),
     (etac notE 5),
     (asm_simp_tac (list_ss addsimps [app_right_Nil]) 5),
     (etac initseg_refl 5),
     (etac notE 5),
     (hyp_subst_tac 5),
     (asm_full_simp_tac (list_ss addsimps [Cons_iff]) 5),
     (etac conjE 5),
     (etac (sym RS app_eq_NilD RS conjE) 5),
     (atac 5),
     (hyp_subst_tac 5),
     (etac (corrX RS CorrectArityD2 RS notE) 5),
     (atac 5),
     (etac exI 5),
     (etac exE 5),
     (hyp_subst_tac 5),
     (etac notE 5),
     (dtac app_typeD 5),
     (atac 5),
     (etac initseg_appI1 5),
     (atac 5),
    (**)
     (ALLGOALS ((etac (Pair_iff RS iffD1 RS conjE)) THEN' hyp_subst_tac)),
     (etac (corrX RS CorrectArityD2 RS notE) 4),
     (atac 4),
     (etac exI 4),
    (**)
     (etac (corrY RS CorrectArityD1 RS exE) 3),
     (atac 3),
     (rtac exI 3),
     (asm_full_simp_tac (IFOL_ss addsimps [app_assoc]) 3),
     (etac (Occ_ShiftI RS Occ_Graft1I2) 3),
    (**)
     (rtac (not_emptyY RS not_emptyE) 2),
     (forward_tac [domY RS subsetD] 2),
     (etac SigmaE 2),
     (hyp_subst_tac 2),
     (etac (hierY RS DenseTreeE) 2),
     (etac initseg_NilI 2),
     (rtac exI 2),
     (eres_inst_tac [("P", "%x. <x, ?X>: ?Y")] (app_right_Nil RS subst) 2),
     (etac (Occ_ShiftI RS Occ_Graft1I2) 2),
    (**)
     (rtac (corrX RS CorrectArityD1 RS exE) 1),
     (REPEAT (atac 1)),
     (rtac exI 1),
     (etac Occ_Graft1I1 1),
     (rtac notI 1),
     (etac notE 1),
     (etac initseg_right_appE 1),
     (REPEAT (atac 1)),
     (eres_inst_tac [("a", "xa")] list.elim 1),
     (asm_simp_tac (list_ss addsimps [app_right_Nil]) 1),
     (etac initseg_refl 1),
     (REPEAT (hyp_subst_tac 1)),
     (asm_full_simp_tac (list_ss addsimps [Cons_iff]) 1),
     (etac conjE 1),
     (etac (sym RS app_eq_NilD RS conjE) 1),
     (atac 1),
     (hyp_subst_tac 1),
     (etac notE 1),
     (rtac refl 1)]);

qed_goal "Occ_shift_in_fin_bnd_set" OccGraft.thy
    "[| X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); b: nat |] \
\      ==> Occ_shift(b, X) : fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  (fn [prem1, prem2] =>
    [(rtac (Occ_fbs_op_bnd_mono RS fin_bnd_set_succI) 1),
     (rtac prem1 2),
     (cut_facts_tac [prem1 RS (fin_bnd_set_domain RS subsetD) RS PowD] 1),
     (rewrite_goals_tac [Occ_fbs_op_def, Occ_fbs_dom_def,
			 list_dom_def, list_op_def]),
     (rtac subsetI 1),
     (etac Occ_shiftE 1),
     (hyp_subst_tac 1),
     (dtac subsetD 1),
     (atac 1),
     (etac SigmaE2 1),
     (rtac SigmaI 1),
     (atac 2),
     (rtac CollectI 1),
     (rewrite_goals_tac list.con_defs),
     (etac (prem2 RS (A_subset_univ RS subsetD) RS Pair_in_univ 
	  RS Inr_in_univ) 1),
     (rtac disjI2 1),
     (REPEAT (ares_tac [exI, refl, conjI, domainI, prem2] 1))]);

qed_goalw "Occ_Shift_in_fin_bnd_set" OccGraft.thy [Occ_fbs_dom_def]
    "[| X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); l: list(nat) |] \
\      ==> Occ_Shift(l, X) : fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  (fn [prem1, prem2] =>
    [(list_ind_tac "l" [prem2] 1),
     (rtac (prem1 RS (fin_bnd_set_domain RS subsetD) RS PowD 
	  RS Occ_Shift_Nil RS ssubst) 1),
     (rtac prem1 1),
     (asm_simp_tac (IFOL_ss addsimps [Occ_Shift_Cons]) 1),
     (fold_goals_tac [Occ_fbs_dom_def]),
     (etac Occ_shift_in_fin_bnd_set 1),
     (atac 1)]);

qed_goalw "Occ_Graft1_in_fin_bnd_set" OccGraft.thy [Occ_Graft1_def]
    "[| X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); \
\       Y: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); l: list(nat) \
\    |] ==> Occ_Graft1(X, l, Y): \
\                  fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  (fn [prem1, prem2, l_list] =>
    [(rtac (Occ_fbs_op_bnd_mono RS fin_bnd_set_UnI) 1),
     (rtac ([Occ_fbs_op_bnd_mono, Diff_subset, prem1] 
	  MRS fin_bnd_set_subsetI) 1),
     (rtac ([prem2, l_list] MRS Occ_Shift_in_fin_bnd_set) 1)]);

qed_goal "Occ_Graft1_not_empty" OccGraft.thy
    "[| Y <= list(nat) * B; Y ~= 0 |] \
\      ==> Occ_Graft1(X, l, Y) ~= 0"
  (fn [domY, not_emptyY] =>
    [(rtac (not_emptyY RS not_emptyE) 1),
     (forward_tac [domY RS subsetD] 1),
     (etac SigmaE 1),
     (hyp_subst_tac 1),
     (rtac not_emptyI 1),
     (etac (Occ_ShiftI RS Occ_Graft1I2) 1)]);

qed_goal "Occ_Graft1_in_Occ_range" OccGraft.thy
    "[| X: Occ_range(Tag, Arity); Y: Occ_range(Tag, Arity); \
\       l: domain(X) |] ==> Occ_Graft1(X, l, Y): Occ_range(Tag, Arity)"
  (fn [domX, domY, l_list] =>
    [(subgoals_tac ["X <= list(nat) * Tag", "Y <= list(nat) * Tag",
		  "l: list(nat)"] 1),
     (rtac (l_list RS domainE) 2),
     (etac (subsetD RS SigmaD1) 2),
     (atac 2),
     (rtac (domY RS Occ_rangeE) 2),
     (etac Occ_fbs_op_lfp_lowerbound 2),
     (rtac (domX RS Occ_rangeE) 2),
     (etac Occ_fbs_op_lfp_lowerbound 2),
     (rtac (domX RS Occ_rangeE) 1),
     (rtac (domY RS Occ_rangeE) 1),
     (cut_facts_tac [l_list] 1),
     (rtac Occ_rangeI 1),
     (rtac ballI 5),
     (dtac bspec 5),
     (dtac bspec 6),
     (REPEAT (atac 5)),
     (ALLGOALS (resolve_tac [Occ_Graft1_in_fin_bnd_set,
			   Occ_Graft1_not_empty,
			   Occ_Graft1_preserves_functionality,
			   Occ_Graft1_preserves_DenseTree,
			   Occ_Graft1_preserves_CorrectArity])),
     (REPEAT (atac 1))]);

qed_goal "Occ_Graft_in_Occ_range" OccGraft.thy
    "[| W: Fin(list(nat)); Incomparable(W); \
\      W <= domain(X); \
\      X: Occ_range(Tag, Arity); Y: Occ_range(Tag, Arity) \
\    |] ==> Occ_Graft(X, W, Y): Occ_range(Tag, Arity)"
  (fn [finW, prem, domW, domX, domY] =>
    [(rtac (domW RS rev_mp) 1),
     (rtac (prem RS rev_mp) 1),
     (rtac (finW RS Fin_induct) 1),
     (ALLGOALS (rtac (impI RS impI))),
     (rtac (Occ_Graft_0 RS ssubst) 1),
     (rtac domX 1),
     (rtac (Occ_Graft_cons RS ssubst) 1),
     (rtac Occ_Graft1_in_Occ_range 5),
     (asm_simp_tac (IFOL_ss addsimps [prove_fun "x ~: y ==> y - {x} = y"]) 5),
     (etac (mp RS mp) 5),
     (etac cons_subsetE 8),
     (etac domainE 8),
     (rtac domainI 8),
     (rtac Occ_GraftI1 8),
     (atac 8),
     (rtac notI 8),
     (etac bexE 8),
     (etac DiffE 8),
     (dtac IncomparableD 8),
     (atac 8),
     (hyp_subst_tac 10),
     (etac (singletonI RSN (2, notE)) 10),
     (etac cons_subsetE 6),
     (etac Incomparable_subset 5),
     (rtac (domX RS Occ_rangeE) 3),
     (rtac (domY RS Occ_rangeE) 4),
     (etac (Occ_fbs_op_lfp_lowerbound) 4),
     (etac (Occ_fbs_op_lfp_lowerbound) 3),
     (REPEAT (ares_tac [domY, consI1, consI2, subset_consI] 1))]);

qed_goal "Occ_Graft_in_Occ_range2" OccGraft.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       Incomparable(W); W <= domain(X); \
\       X: Occ_range(Tag, Arity); Y: Occ_range(Tag, Arity) \
\    |] ==> Occ_Graft(X, W, Y): Occ_range(Tag, Arity)"
  (fn [hcons, hind, prem, domW, domX, domY] =>
    [(rtac Occ_Graft_in_Occ_range 1),
     (rtac (domW RS Fin_subset) 1),
     (rtac Fin_domainI 1),
     (rtac ([hcons, domX] MRS Occ_range_convert_lemma) 1),
     (etac (hind RS Occ_ind_cond_Occ_FinI) 1),
     (REPEAT (ares_tac [prem, domW, domX, domY] 1))]);

(** subst **)
qed_goal "def_graft_type" OccGraft.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       !!x W y. graft(x, W, y) == Occinv(Occ_Graft(Occ(x), W, Occ(y))); \
\       M: Terms; N: Terms; \
\       Incomparable(W); W <= domain(Occ(M)) \
\   |] ==> graft(M, W, N): Terms"
  (fn hcons::hind::hinv::hsubst::prems =>
    [(rewrite_goals_tac [hsubst]),
     (cut_facts_tac prems 1),
     (rtac ([hcons, hind, hinv] MRS def_Occinv_type) 1),
     (rtac ([hcons, hind] MRS Occ_Graft_in_Occ_range2) 1),
     (REPEAT (ares_tac [hind RS Occ_ind_cond_Occ_in_Occ_range] 1))]);

qed_goal "def_graft_0" OccGraft.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       !!x W y. graft(x, W, y) == Occinv(Occ_Graft(Occ(x), W, Occ(y))); \
\       M: Terms \
\   |] ==> graft(M, 0, N) = M"
  (fn [hcons, hind, hinv, hsubst, prem] =>
    [(rewrite_goals_tac [hsubst]),
     (cut_facts_tac [prem] 1),
     (asm_simp_tac (IFOL_ss addsimps
		  [[hcons, hind, hinv] MRS def_Occinv_Occ,
		   Occ_Graft_0]) 1)]);

qed_goal "def_graft_Nil" OccGraft.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       !!x W y. graft(x, W, y) == Occinv(Occ_Graft(Occ(x), W, Occ(y))); \
\       M: Terms; N: Terms \
\   |] ==> graft(M, {[]}, N) = N"
  (fn hcons::hind::hinv::hsubst::prems =>
    [(rewrite_goals_tac [hsubst]),
     (cut_facts_tac prems 1),
     (subgoals_tac ["Occ(M) <= list(nat) * Tag",
		  "Occ(N) <= list(nat) * Tag"] 1),
     (asm_simp_tac (IFOL_ss addsimps 
		  [[hcons, hind, hinv] MRS def_Occinv_Occ,
		   Occ_Graft_Nil]) 1),
     (REPEAT (ares_tac [hind RS Occ_ind_cond_Occ_domain] 1))]);

qed_goal "def_graft" OccGraft.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       Term_cons_inj_cond(Terms, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       !!x W y. graft(x, W, y) == Occinv(Occ_Graft(Occ(x), W, Occ(y))); \
\       Term_cons(T, l): Terms; \
\       T: Tag; l: list(Terms); Arity(T) = length(l); y: Terms; \
\       W ~= {[]}; Incomparable(W); \
\       W <= domain(Occ(Term_cons(T, l)))\
\   |] ==> graft(Term_cons(T, l), W, y) = \
\        Term_cons(T, mapnth(%z r. graft(r, lists_subtree(z, W), y), l))"
  (fn hcons::hind::hinj::hinv::hsubst::prems =>
    [(rewrite_goals_tac [hsubst]),
     (cut_facts_tac prems 1),
     (subgoals_tac ["map(Occ, l): list(Pow(list(nat)*Tag))",
		  "Arity(T) = length(map(Occ, l))",
		  "Occ(y) <= list(nat) * Tag",
		  "Occ_Graft(Occ(Term_cons(T, l)), W, Occ(y)) \
		  \         : Occ_range(Tag, Arity)"] 1),
     (asm_full_simp_tac (IFOL_ss addsimps 
			 [[hind, hinj] MRS Occ_Term_cons,
			  Occ_Graft_Occ_cons, mapnth_map]) 1),
     (rtac ([hcons, hind, hinv] MRS def_Occinv2 RS trans) 1),
     (asm_simp_tac (nth_ss addsimps [map_mapnth]) 5),
     (asm_simp_tac (nth_ss addsimps [length_mapnth]) 4),
     (asm_simp_tac (nth_ss addsimps [length_map]) 6),
     (rtac nth_convert_list_type 3),
     (etac mapnth_type2 3),
     (asm_simp_tac (nth_ss addsimps [nth_mapnth, length_mapnth]) 3),
     (rtac ballI 3),
     (rtac (Occ_Graft_domain RS PowI) 3),
     (rtac map_type 8),
     (rtac ([hcons, hind] MRS Occ_Graft_in_Occ_range2) 6),
     (TRYALL atac),
     (rtac PowI 6),
     (TRYALL (eresolve_tac [hind RS Occ_ind_cond_Occ_domain,
			  hind RS Occ_ind_cond_Occ_in_Occ_range])),
     (etac (nth_type2 RS (hind RS Occ_ind_cond_Occ_domain)) 1),
     (asm_full_simp_tac nth_ss 1),
     (res_inst_tac [("P", "%x. ?X <= x")] subst 1),
     (etac lists_subtree_mono 2),
     (subgoals_tac ["x: nat"] 1),
     (asm_simp_tac (nth_ss addsimps [lists_subtree_domain_eq,
				    Occ_subtree_Occ_cons,
				    nth_map]) 1),
     (rtac (length_type RSN (2, mem_nat_in_nat)) 1),
     (atac 2),
     (asm_full_simp_tac nth_ss 1)]);
