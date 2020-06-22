(*
    File:        InitSeg.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open InitSeg;

qed_goal "app_typeD" List.thy
    "[| l @ m: list(A); l: list(A) |] ==> m: list(A)"
  (fn [major, prem] =>
    [(rtac (major RS rev_mp) 1),
     (list_ind_tac "l" [prem] 1),
     (ALLGOALS (asm_simp_tac nth_ss)),
     (rtac impI 1),
     (etac ConsE 1),
     (etac mp 1),
     (atac 1)]);

qed_goal "app_Un_type" List.thy
    "!! a b. [| a: list(A); b: list(B) |] ==> a @ b: list(A Un B)"
  (fn _ =>
    [(rtac app_type 1),
     (etac (Un_upper1 RS list_mono RS subsetD) 1),
     (etac (Un_upper2 RS list_mono RS subsetD) 1)]);

qed_goal "app_right_inj" List.thy
    "[| l@m = l@n; l: list(A) |] ==> m = n"
  (fn [prem, major] =>
    [(rtac (prem RS rev_mp) 1),
     (list_ind_tac "l" [major] 1),
     (REPEAT (resolve_tac [allI, impI] 2)),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps [Cons_iff]))),
     (mp_tac 1),
     (atac 1)]);

qed_goal "app_right_inj_iff" List.thy
    "l: list(A) ==> l@m = l@n <-> m = n"
  (fn [prem] =>
    [(rtac iffI 1),
     (etac (prem RSN (2, app_right_inj))  1),
     (etac subst 1),
     (rtac refl 1)]);

qed_goal "app_last_eqD" List.thy
    "[| l @ [a] = m @ [b]; l: list(A); m: list(B) |] ==> \
\        l = m & a = b"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (prem2 RS rev_bspec) 1),
     (rtac (prem1 RS list.induct) 1),
     (ALLGOALS (rtac ballI)),
     (eres_inst_tac [("a", "x")] list.elim 2),
     (eres_inst_tac [("a", "x")] list.elim 1),
     (eres_inst_tac [("a", "l")] list.elim 3),
     (eres_inst_tac [("a", "l")] list.elim 2),
     (ALLGOALS (asm_full_simp_tac nth_ss)),
     (rtac impI 5),
     (etac (bspec RS mp) 5),
     (safe_tac (ZF_cs addSEs list.free_SEs))]);

qed_goal "app_last_iff" List.thy
    "!!l m. [| l: list(A); m: list(B) |] ==> \
\           l @ [a] = m @ [b] <-> l = m & a = b"
  (fn _ =>
    [(fast_tac (ZF_cs addSDs [app_last_eqD]) 1)]);

qed_goal "app_left_inj" List.thy
    "[| a@c = b@c; a: list(A); b: list(B); c: list(C) |] ==> a = b"
  (fn [prem, major, prem1, prem2] =>
    [(rtac (prem RS rev_mp) 1),
     (rtac (prem1 RS rev_bspec) 1),
     (rtac (major RS rev_bspec) 1),
     (rtac (prem2 RS list_append_induct) 1),
     (ALLGOALS (asm_simp_tac (nth_ss addsimps [app_assoc RS sym]))),
     (fast_tac (ZF_cs addSDs [app_last_eqD] addSIs [app_Un_type]) 1)]);

qed_goal "app_left_inj_iff" List.thy
    "[| a: list(A); b: list(A); c: list(A) |] ==> a@c = b@c <-> a = b"
  (fn prems =>
    [(rtac iffI 1),
     (etac app_left_inj 1),
     (REPEAT (ares_tac prems 1)),
     (etac subst 1),
     (rtac refl 1)]);

qed_goal "app_appE_lemma" List.thy
    "m: list(A) ==> ALL l: list(A). m @ x = l @ y --> \
\         (EX z. l = m @ z) | (EX z. m = l @ z)"
  (fn [prem] =>
    [(list_ind_tac "m" [prem] 1),
     (ALLGOALS (asm_simp_tac nth_ss)),
     (ALLGOALS (rtac (impI RS ballI))),
     (rtac disjI1 1),
     (rtac (refl RS exI) 1),
     (eres_inst_tac [("a", "xa")] list.elim 1),
     (ALLGOALS hyp_subst_tac),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps [Cons_iff]))),
     (rtac disjI2 1),
     (rtac (refl RS exI) 1)]);

qed_goal "app_appE" List.thy
    "[| m @ x = l @ y; m: list(A); l: list(A); \
\       !! z. [| z: list(A); l = m @ z; x = z @ y |] ==> R; \
\       !! z. [| z: list(A); m = l @ z; y = z @ x |] ==> R \
\    |] ==> R"
  (fn [major, m_list, l_list, prem1, prem2] =>
    [(cut_facts_tac [m_list, l_list, major] 1),
     (rtac (m_list RS app_appE_lemma RS bspec RS mp RS disjE) 1),
     (rtac l_list 1),
     (rtac major 1),
     (ALLGOALS (etac exE)),
     (rtac prem2 2),
     (rtac prem1 1),
     (ALLGOALS hyp_subst_tac),
     (TRYALL ((etac app_typeD) THEN' atac ORELSE' (rtac refl))),
     (ALLGOALS (asm_full_simp_tac (IFOL_ss addsimps [app_assoc,
						   app_right_inj_iff])))]);

qed_goal "app_Nil_eqD1" List.thy
    "[| a@b = a; a:list(A) |] ==> b = []"
  (fn [major, prem] =>
    [(rtac (major RS rev_mp) 1),
     (list_ind_tac "a" [prem] 1),
     (ALLGOALS (asm_simp_tac nth_ss))]);

qed_goal "app_Nil_eqD2" List.thy
    "[| a@b = b; a: list(A); b: list(B) |] ==> a = []"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (prem1 RSN (2, bspec)) 1),
     (rtac (prem2 RS list_append_induct) 1),
     (rtac ballI 2),
     (dres_inst_tac [("x", "xa")] bspec 2),
     (ALLGOALS (asm_simp_tac (nth_ss addsimps [app_assoc RS sym]))),
     (fast_tac (ZF_cs addSDs [app_last_eqD] addIs [app_Un_type]) 1)]);

qed_goal "app_eq_Nil_iff" List.thy
    "a: list(A) ==> a @ b = [] <-> a = [] & b = []"
  (fn [major] =>
    [(list_ind_tac "a" [major] 1),
     (ALLGOALS (asm_simp_tac nth_ss)),
     (fast_tac (ZF_cs addSEs list.free_SEs) 1)]);

qed_goal "app_eq_NilD" List.thy
    "[| a @ b = []; a: list(A) |] ==> a = [] & b = []"
  (fn [major, prem] =>
    [(rtac ([prem, major] MRS (app_eq_Nil_iff RS iffD1)) 1)]);

qed_goal "app_antisym" List.thy
    "[| a @ c = b; b @ d = a; \
\      a: list(A); b: list(B); c: list(C); d:list(D) \
\    |] ==> a = b"
  (fn prem1::prem2::prems =>
    [(cut_facts_tac (prems @ [prem1, prem2]) 1),
     (hyp_subst_tac 1),
     (asm_full_simp_tac (IFOL_ss addsimps [app_assoc]) 1),
     (safe_tac (ZF_cs addSDs [app_Nil_eqD1, app_eq_NilD])),
     (REPEAT (atac 1)),
     (asm_simp_tac nth_ss 1)]);

qed_goal "app_antisym2" List.thy
    "[| c @ a = b; d @ b = a; \
\      a: list(A); b: list(B); c: list(C); d:list(D) \
\    |] ==> a = b"
  (fn prem1::prem2::prems =>
    [(cut_facts_tac (prems @ [prem1, prem2]) 1),
     (hyp_subst_tac 1),
     (asm_full_simp_tac (IFOL_ss addsimps [app_assoc RS sym]) 1),
     (safe_tac (ZF_cs addSDs [app_Nil_eqD2, app_eq_NilD])),
     (REPEAT (ares_tac [app_Un_type] 1)),
     (asm_simp_tac nth_ss 1)]);

(** initseg **)
qed_goalw "initsegI" InitSeg.thy [initseg_def]
    "!!a. [| a@x = b; x: list(A); a: list(A); b: list(A) |] \
\          ==> initseg(A, a, b)"
  (fn _ =>
    [(REPEAT (ares_tac [conjI, bexI] 1))]);

qed_goalw "initsegD1" InitSeg.thy [initseg_def]
    "initseg(A, a, b) ==> a: list(A)"
  (fn [major] =>
    [(rtac (major RS conjunct1) 1)]);

qed_goalw "initsegD2" InitSeg.thy [initseg_def]
    "initseg(A, a, b) ==> b: list(A)"
  (fn [major] =>
    [(rtac (major RS conjunct2 RS conjunct1) 1)]);

qed_goalw "initsegE" InitSeg.thy [initseg_def]
    "[| initseg(A, a, b); \
\       !!x. [| a: list(A); b: list(A); x: list(A); b = a@x |] ==> R\
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac [conjE, bexE] 1)),
     (rtac prem 1),
     (etac sym 4),
     (REPEAT (atac 1))]);

qed_goalw "initseg_antisym" InitSeg.thy [initseg_def]
    "[| initseg(A, x, y); initseg(A, y, x) |] ==> x = y"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (eresolve_tac [conjE, bexE] 1)),
     ((etac app_antisym 1) THEN (atac 1)),
     (REPEAT (atac 1))]);

qed_goalw "initseg_trans" InitSeg.thy [initseg_def]
    "!! m. [| initseg(A, x, y); initseg(A, y, z) |] ==> initseg(A, x, z)"
  (fn _ =>
    [(safe_tac ZF_cs),
     (asm_simp_tac (nth_ss addsimps [app_assoc]) 1),
     (REPEAT (ares_tac [bexI, app_type, refl] 1))]);

qed_goalw "initseg_refl" InitSeg.thy [initseg_def]
    "x: list(A) ==> initseg(A, x, x)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_full_simp_tac nth_ss 1),
     (rtac bexI 1),
     (etac app_right_Nil 1),
     (resolve_tac list.intrs 1)]);

qed_goalw "initseg_appI1" InitSeg.thy [initseg_def]
    "[| x: list(A); y: list(A) |] ==> initseg(A, x, x@y)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_simp_tac nth_ss 1),
     (rtac conjI 1),
     (asm_simp_tac nth_ss 1),
     (rtac bexI 1),
     (rtac refl 1),
     (atac 1)]);

qed_goalw "initseg_appI2" InitSeg.thy [initseg_def]
    "[| x: list(A); initseg(A, y, z) |] ==> initseg(A, x@y, x@z)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (eresolve_tac [conjE, bexE] 1)),
     (rtac conjI 1),
     (asm_simp_tac nth_ss 1),
     (rtac conjI 1),
     (asm_simp_tac nth_ss 1),
     (hyp_subst_tac 1),
     (rtac bexI 1),
     (rtac app_assoc 1),
     (REPEAT (atac 1))]);

qed_goalw "initseg_NilI" InitSeg.thy [initseg_def]
    "x: list(A) ==> initseg(A, [], x)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_simp_tac nth_ss 1),
     (fast_tac (ZF_cs addIs list.intrs) 1)]);

qed_goalw "initseg_ConsI" InitSeg.thy [initseg_def]
    "[| a: A; initseg(A, y, z) |] ==> initseg(A, Cons(a, y), Cons(a, z))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (eresolve_tac [conjE, bexE] 1)),
     (REPEAT (ares_tac ([conjI] @ list.intrs) 1)),
     (hyp_subst_tac 1),
     (rtac bexI 1),
     (rtac app_Cons 1),
     (atac 1)]);

qed_goalw "initseg_NilE" InitSeg.thy [initseg_def]
    "[| initseg(A, l, []); l = [] ==> R |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac [conjE, bexE] 1)),
     (rtac prem 1),
     (etac (app_eq_NilD RS conjunct1) 1),
     (atac 1)]);

qed_goalw "initseg_ConsE" InitSeg.thy [initseg_def]
    "[| initseg(A, l, Cons(b, m)); \
\       l = [] ==> R;\
\       !!n. [| initseg(A, n, m); b: A; l = Cons(b, n) |] ==> R |] ==> R"
  (fn [prem, nil_case, cons_case] =>
    [(cut_facts_tac [prem] 1),
     (REPEAT (eresolve_tac [conjE, bexE] 1)),
     (etac list.elim 1),
     (etac nil_case 1),
     (rtac cons_case 1),
     (etac ConsE 2),
     (atac 2),
     (hyp_subst_tac 2),
     (asm_full_simp_tac (nth_ss addsimps [Cons_iff]) 2),
     (hyp_subst_tac 1),
     (etac ConsE 1),
     (asm_full_simp_tac (nth_ss addsimps [Cons_iff]) 1),
     (rtac bexI 1),
     (etac conjunct2 1),
     (atac 1)]);

qed_goalw "initseg_left_ConsE" InitSeg.thy [initseg_def]
    "[| initseg(A, Cons(b, l), m); \
\       !!n. [| m = Cons(b, n); b: A; initseg(A, l, n) |] ==>R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac [conjE, bexE] 1)),
     (asm_full_simp_tac nth_ss 1),
     (etac (sym RS prem) 1),
     (ALLGOALS (etac ConsE)),
     (REPEAT (ares_tac [conjI, app_type, refl, bexI] 1))]);

qed_goalw "initseg_left_appE" InitSeg.thy [initseg_def]
    "[| initseg(A, a@b, c); a: list(A); \
\       !!l. [| c = a@l; initseg(A, b, l) |] ==>R \
\    |] ==> R"
  (fn [major, prem1, prem2] =>
    [(cut_facts_tac [major, prem1] 1),
     (REPEAT (eresolve_tac [conjE, bexE] 1)),
     (dtac app_typeD 1),
     (atac 1),
     (asm_full_simp_tac (nth_ss addsimps [app_assoc]) 1),
     (etac (sym RS prem2) 1),
     (REPEAT (ares_tac [conjI, app_type, refl, bexI] 1))]);

qed_goal "initseg_right_appE" InitSeg.thy
    "[| initseg(A, l, m@n); \
\       m: list(A); \
\       [| n: list(A); initseg(A, l, m) |] ==> R; \
\       !!x y. [| x: list(A); y: list(A); n: list(A); l = m @ x; n = x @ y; \
\                 initseg(A, m, l) |] ==> R \
\    |] ==> R"
  (fn [major, m_list, prem1, prem2] =>
    [(cut_facts_tac [m_list] 1),
     (rtac (major RS initsegE) 1),
     (subgoals_tac ["n: list(A)"] 1),
     (etac app_typeD 2),
     (rtac m_list 2),
     (rtac (app_appE_lemma RS bspec RS mp RS disjE) 1),
     (atac 3),
     (REPEAT (atac 1)),
     (ALLGOALS (etac exE)),
     (rtac prem1 2),
     (rtac prem2 1),
     (atac 4),
     (ALLGOALS hyp_subst_tac),
     (asm_full_simp_tac (nth_ss addsimps [app_right_inj_iff, 
					 app_assoc]) 4),
     (TRYALL atac),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps [app_right_inj_iff, 
						   app_assoc]))),
     (rtac initseg_appI1 2),
     (rtac initseg_appI1 4),
     (REPEAT ((atac 1) ORELSE (etac app_typeD 1)))]);

qed_goal "initseg_app_lastE" InitSeg.thy
    "[| initseg(A, l, m@[b]); m: list(A); \
\       l = m @ [b] ==> R;\
\       [| initseg(A, l, m); b: A |] ==> R\
\     |] ==> R"
  (fn [major, prem, prem1, prem2] =>
    [(cut_facts_tac [prem] 1),
     (rtac (major RS initseg_right_appE) 1),
     (rtac prem 1),
     (rtac prem2 1),
     (etac ConsE 2),
     (REPEAT (atac 1)),
     (res_inst_tac [("Q", "initseg(A, l, m)")] (excluded_middle RS disjE) 1),
     (rtac prem2 2),
     (etac ConsE 3),
     (REPEAT (atac 2)),
     (rtac prem1 1),
     (hyp_subst_tac 1),
     (eres_inst_tac [("a", "x")] list.elim 1),
     (ALLGOALS hyp_subst_tac),
     (etac notE 1),
     (asm_simp_tac (IFOL_ss addsimps [app_right_Nil]) 1),
     (etac initseg_refl 1),
     (asm_full_simp_tac (nth_ss addsimps [Cons_iff]) 1),
     (etac conjE 1),
     (dtac (sym RS app_eq_NilD) 1),
     (etac conjE 2),
     (asm_simp_tac nth_ss 2),
     (atac 1)]);


(** We can regard a list as a poset under initseg **)

qed_goal "poset_initseg" InitSeg.thy
    "poset(initseg(A), list(A))"
  (fn _ =>
    [(rtac posetI 1),
     (etac initseg_refl 1),
     (etac initseg_antisym 1),
     (etac initseg_trans 2),
     (REPEAT (atac 1))]);

qed_goal "initseg_downset_forms_a_chain" InitSeg.thy
    "l: list(A) ==> chain(initseg(A), downset(initseg(A), list(A), l))"
  (fn [major] =>
    [(rtac chainI 1),
     (rtac (poset_initseg RS (downset_subset RS poset_subset)) 1),
     (fast_tac (ZF_cs addSEs [downsetE, initsegE, app_appE]
	      addSIs [initseg_appI1]) 1)]);

qed_goalw "initseg_appI3" InitSeg.thy [initseg_def]
    "[| initseg(A, y, z); x: list(A) |] ==> initseg(A, y, z@x)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (eresolve_tac [conjE, bexE] 1)),
     (REPEAT (ares_tac [conjI, app_type] 1)),
     (rtac bexI 1),
     (hyp_subst_tac 1),
     (dtac app_typeD 1),
     (asm_simp_tac (nth_ss addsimps [app_assoc]) 2),
     (REPEAT (ares_tac [app_type] 1))]);

qed_goal "initseg_downset_is_Finite" InitSeg.thy
    "l: list(A) ==> Finite(downset(initseg(A), list(A), l))"
  (fn [major] =>
    [(rtac (major RS list_append_induct) 1),
     (res_inst_tac [("P", "%x. Finite(x)")] ssubst 1),
     (rtac Finite_cons 2),
     (rtac Finite_0 2),
     (res_inst_tac [("P", "%x. Finite(x)")] ssubst 2),
     (etac Finite_cons 3),
     (ALLGOALS (rtac equalityI)),
     (safe_tac (ZF_cs addSEs [downsetE, initseg_NilE])),
     (rtac refl 1),
     (rtac downsetI 1),
     (rtac downsetI 4),
     (rtac initseg_refl 5),
     (rtac downsetI 6),
     (etac initseg_appI3 7),
     (REPEAT (ares_tac (list.intrs @ [initseg_NilI]) 1)),
     (REPEAT (ares_tac (list.intrs @ [app_type]) 2)),
     (etac initseg_right_appE 1),
     (eres_inst_tac [("a", "xb")] list.elim 3),
     (REPEAT (hyp_subst_tac 3)),
     (rotate_tac 10 4),
     (asm_full_simp_tac nth_ss 4),
     (safe_tac (ZF_cs addSDs [sym RS app_eq_NilD])),
     (asm_simp_tac nth_ss 4),
     (asm_full_simp_tac nth_ss 2),
     (atac 3),
     (ALLGOALS (swap_res_tac [downsetI])),
     (REPEAT (ares_tac [initseg_refl] 1))]);
