(*
    File:        SubOcc.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open SubOcc;

(** Occ_Subtree **)
qed_goalw "Occ_SubtreeI" SubOcc.thy [Occ_Subtree_def]
    "[| m: list(A); <m@l, T>: X |] ==> <l, T>: Occ_Subtree(m, X)"
  (fn [m_list, prem] =>
    [(cut_facts_tac [prem, m_list] 1),
     (rtac ReplaceI 1),
     (atac 2),
     (REPEAT (resolve_tac [refl, conjI, exI] 1)),
     (REPEAT (eresolve_tac [exE, conjE] 1)),
     (asm_full_simp_tac (IFOL_ss addsimps [Pair_iff, app_right_inj_iff]) 1)]);

qed_goalw "Occ_SubtreeD" SubOcc.thy [Occ_Subtree_def]
    "<l, T>: Occ_Subtree(m, X) ==> <m@l, T>: X"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac ZF_cs 1)]);

qed_goalw "Occ_SubtreeE" SubOcc.thy [Occ_Subtree_def]
    "[| x: Occ_Subtree(m, X); \
\       !!l T. [| x = <l, T>; <m@l, T>: X |] ==> R |]==> R"
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

val Occ_SubtreeE2 = standard(make_elim(Occ_SubtreeD));

qed_goalw "Occ_Subtree_0" SubOcc.thy [Occ_Subtree_def]
    "Occ_Subtree(m, 0) = 0"
  (fn _ =>
    [(fast_tac eq_cs 1)]);

qed_goalw "Occ_Subtree_Nil" SubOcc.thy [Occ_Subtree_def]
    "X <= A * B ==> Occ_Subtree([], X) = X"
  (fn [prem] =>
    [(simp_tac list_ss 1),
     (cut_facts_tac [prem] 1),
     (fast_tac eq_cs 1)]);

qed_goalw "Occ_Subtree_Cons" SubOcc.thy [Occ_Subtree_def]
    "l: list(A) ==> \
\       Occ_Subtree(Cons(a, l), X) = Occ_Subtree(l, Occ_subtree(a, X))"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (simp_tac list_ss 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [Occ_subtreeE])),
     (rtac ReplaceI 1),
     (etac Occ_subtreeI 2),
     (rtac ReplaceI 3),
     (atac 4),
     (REPEAT (ares_tac [refl, exI, conjI] 3)),
     (REPEAT (ares_tac [refl, exI, conjI] 1)),
     (ALLGOALS (REPEAT o (eresolve_tac [exE, conjE]))),
     (ALLGOALS (asm_full_simp_tac (list_ss addsimps [Cons_iff, 
						   app_right_inj_iff])))]);

qed_goal "Occ_Subtree_app" SubOcc.thy
    "[| l: list(A); m: list(A); X <= list(C) * D |] ==> \
\         Occ_Subtree(l@m, X) = Occ_Subtree(m, Occ_Subtree(l, X))"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem3 RS rev_mp) 1),
     (res_inst_tac [("x", "X")] spec 1),
     (list_ind_tac "l" [prem1] 1),
     (cut_facts_tac [prem2] 2),
     (ALLGOALS (asm_simp_tac (list_ss addsimps [Occ_Subtree_Nil,
					      Occ_Subtree_Cons]))),
     (rtac (impI RS allI) 1),
     (dtac Occ_subtree_preserves_domain 1),
     (dtac spec 1),
     (mp_tac 1),
     (atac 1)]);

qed_goal "Occ_Subtree_in_Occ_range" SubOcc.thy
    "[| <l, T>: X; X: Occ_range(Tag, Arity) |] ==>\
\                Occ_Subtree(l, X): Occ_range(Tag, Arity)"
  (fn [major, prem] =>
    [(rtac (prem RS rev_mp) 1),
     (rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "X")] spec 1),
     (list_ind_tac "l" [major RS (prem RS Occ_range_domain_lemma RS subsetD 
				RS SigmaD1)] 1),
     (ALLGOALS (rtac (impI RS impI RS allI))),
     (ALLGOALS (forward_tac [Occ_range_domain_lemma])),
     (ALLGOALS (asm_simp_tac (list_ss addsimps [Occ_Subtree_Nil,
					      Occ_Subtree_Cons]))),
     (etac (spec RS mp RS mp) 1),
     (etac Occ_subtreeI 1),
     (rtac Occ_subtree_in_Occ_range 1),
     (REPEAT (atac 1))]);

(** Term_cons_inj_cond **)
qed_goalw "Term_cons_inj_condI" SubOcc.thy [Term_cons_inj_cond_def]
    "[| !! T U l m. \
\     [| T: Tag; U: Tag; l: list(Terms); m: list(Terms); \
\       Term_cons(T, l): Terms \
\     |] ==> Term_cons(T, l) = Term_cons(U, m) <-> \
\           T = U & (ALL z: Arity(T). nth(l, z) = nth(m, z)) \
\    |] ==> Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)"
  (fn prems =>
    [(REPEAT (resolve_tac [ballI, impI] 1)),
     (REPEAT (ares_tac prems 1))]);

qed_goalw "Term_cons_inj_condD" SubOcc.thy [Term_cons_inj_cond_def]
    "[| Term_cons_inj_cond(Terms, Tag, Arity, Term_cons); \
\       T: Tag; U: Tag; l: list(Terms); m: list(Terms); \
\       Term_cons(T, l): Terms \
\    |] ==> Term_cons(T, l) = Term_cons(U, m) <-> \
\            T = U & (ALL z: Arity(T). nth(l, z) = nth(m, z))"
  (fn major::prems =>
    [(rtac (major RS bspec RS bspec RS bspec RS bspec RS mp) 1),
     (REPEAT (ares_tac prems 1))]);

qed_goalw "Term_cons_inj_condD1" SubOcc.thy [Term_cons_inj_cond_def]
    "[| Term_cons_inj_cond(Terms, Tag, Arity, Term_cons); \
\       Term_cons(T, l) = Term_cons(U, m); \
\       T: Tag; U: Tag; l: list(Terms); m: list(Terms); \
\       Term_cons(T, l): Terms \
\    |] ==> T = U & (ALL z: Arity(T). nth(l, z) = nth(m, z))"
  (fn major::prems =>
    [(rtac (major RS bspec RS bspec RS bspec RS bspec RS mp RS iffD1) 1),
     (REPEAT (ares_tac prems 1))]);

qed_goal "Occ_ind_cond_Term_cons_lemma" SubOcc.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       M: Terms |] ==> EX T: Tag. EX l: list(Terms). \
\           M = Term_cons(T, l) & Arity(T) = length(l)"
  (fn [hind, major] =>
    [(rtac ([hind, major] MRS Occ_ind_condD) 1),
     (REPEAT (ares_tac [refl, bexI, conjI] 1))]);

qed_goal "Term_cons_inj_cond_induct_lemma" SubOcc.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       Term_cons_inj_cond(Terms, Tag, Arity, Term_cons); \
\       M: Terms; \
\       !! l T. [| T: Tag; l: list(Terms); \
\             Term_cons(T, l): Terms; \
\             Arity(T) = length(l); \
\             Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l)); \
\             ALL z: length(l). ALL U: Tag. ALL m: list(Terms). \
\                nth(l, z) = Term_cons(U, m) & Arity(U) = length(m) \
\                --> P(nth(l, z), U, m)\
\       |]  ==> P(Term_cons(T, l), T, l) \
\    |] ==> ALL T. ALL l. M = Term_cons(T, l) & Arity(T) = length(l) & \
\           T: Tag & l: list(Terms) --> P(M, T, l)"
  (fn [hind, hinj, major, indstep] =>
    [(rtac ([hind, major] MRS Occ_ind_condD) 1),
     (rtac (impI RS allI RS allI) 1),
     (REPEAT (etac conjE 1)),
     (dtac (hinj RS Term_cons_inj_condD1) 1),
     (REPEAT (atac 1)),
     (etac conjE 1),
     (hyp_subst_tac 1),
     (subgoals_tac ["l = xa"] 1),
     (rtac nth_inj 2),
     (asm_full_simp_tac IFOL_ss 2),
     (asm_full_simp_tac IFOL_ss 2),
     (REPEAT (atac 2)),
     (hyp_subst_tac 1),
     (rtac indstep 1),
     (REPEAT (atac 1)),
     (REPEAT (resolve_tac [ballI, impI] 1)),
     (etac conjE 1),
     (dtac bspec 1),
     (atac 1),
     (dtac (spec RS spec RS mp) 1),
     (REPEAT (ares_tac [conjI] 1))]);

qed_goal "Term_cons_inj_cond_induct" SubOcc.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       Term_cons_inj_cond(Terms, Tag, Arity, Term_cons); \
\       Term_cons(T, l): Terms; \
\       T: Tag; l: list(Terms); Arity(T) = length(l); \
\       !! l T. [| T: Tag; l: list(Terms); \
\             Term_cons(T, l): Terms; \
\             Arity(T) = length(l); \
\             Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l)); \
\             ALL z: length(l). ALL U: Tag. ALL m: list(Terms). \
\                nth(l, z) = Term_cons(U, m) & Arity(U) = length(m) \
\                --> P(U, m)\
\       |]  ==> P(T, l) \
\    |] ==> P(T, l)"
  (fn [hind, hinj, major, t_tag, l_list, lencond, indstep] =>
    [(rtac ([hind, hinj, major] MRS Term_cons_inj_cond_induct_lemma
	  RS spec RS spec RS mp) 1),
     (REPEAT (ares_tac [refl, t_tag, l_list, lencond, conjI] 2)),
     (rtac indstep 1),
     (REPEAT (atac 1))]);

qed_goal "Occ_Term_cons" SubOcc.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       Term_cons_inj_cond(Terms, Tag, Arity, Term_cons); \
\       Term_cons(T, l): Terms; \
\       T: Tag; l: list(Terms); Arity(T) = length(l) \
\    |] ==> Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l))"
  (fn hind::hinj::prems =>
    [(rtac (prems MRS ([hind, hinj] MRS Term_cons_inj_cond_induct)) 1),
     (atac 1)]);

qed_goal "def_Sub_type" SubOcc.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       !!M. Sub(M) == {<l, Occinv(Occ_Subtree(l, Occ(M)))>. <l, T>: Occ(M)}; \
\       M: Terms \
\    |] ==> Sub(M) <= list(nat)*Terms"
  (fn [hcons, hind, hinv, hsub, major] =>
    [(rewrite_goals_tac [hsub]),
     (safe_tac ZF_cs),
     (forward_tac [[hind, major] MRS Occ_ind_cond_Occ_domain RS subsetD] 1),
     (etac SigmaE 1),
     (hyp_subst_tac 1),
     (asm_simp_tac list_ss 1),
     (cut_facts_tac [major] 1),
     (fast_tac (ZF_cs addIs [[hcons, hind, hinv] MRS def_Occinv_type,
			   Occ_Subtree_in_Occ_range,
			   hind RS Occ_ind_cond_Occ_in_Occ_range]) 1)]);

qed_goal "def_Sub_rec" SubOcc.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       !!M. Sub(M) == {<l, Occinv(Occ_Subtree(l, Occ(M)))>. <l, T>: Occ(M)}; \
\       Term_cons_inj_cond(Terms, Tag, Arity, Term_cons); \
\       Term_cons(T, l): Terms; \
\       T: Tag; l: list(Terms); Arity(T) = length(l) \
\    |] ==> Sub(Term_cons(T, l)) = Occ_cons(Term_cons(T, l), map(Sub, l))"
  (fn hcons::hind::hinv::hsub::hinj::prems =>
    [(rewrite_goals_tac [hsub]),
     (rtac (prems MRS ([hind, hinj] MRS Term_cons_inj_cond_induct)) 1),
     (safe_tac eq_cs),
     (forward_tac [hind RS Occ_ind_cond_Occ_domain] 1),
     (forward_tac [subsetD] 1),
     (atac 1),
     (etac SigmaE 1),
     (hyp_subst_tac 1),
     (simp_tac nth_ss 1),
     (res_inst_tac [("a", "xb")] list.elim 1),
     (atac 1),
     (TRYALL hyp_subst_tac),
     (dres_inst_tac [("a", "Occ(?X)")] sym 1),
     (asm_simp_tac (nth_ss addsimps [[hcons, hind, hinv] MRS
				    def_Occinv_Occ,
				    Occ_Subtree_Nil]) 1),
     (rtac Occ_consI1 1),
     (asm_full_simp_tac IFOL_ss 1),
     (etac Occ_cons_ConsE 1),
     (subgoals_tac ["map(Occ, l): list(Pow(list(nat) * Tag))"] 1),
     (asm_simp_tac (nth_ss addsimps [length_map, Occ_subtree_Occ_cons,
				   Occ_Subtree_Cons]) 1),
     (rtac Occ_consI2 1),
     (asm_full_simp_tac (list_ss addsimps [length_map]) 1),
     (asm_full_simp_tac (nth_ss addsimps [nth_map, length_map]) 1),
     (rewrite_goals_tac [hsub]),
     (rtac RepFun_eqI 1),
     (atac 2),
     (asm_simp_tac nth_ss 1),
     (rtac map_type 1),
     (atac 1),
     (etac (hind RS Occ_ind_cond_Occ_domain RS PowI) 1),
     (etac Occ_consE 1),
     (ALLGOALS hyp_subst_tac),
     (rtac RepFun_eqI 1),
     (asm_simp_tac IFOL_ss 2),
     (rtac Occ_consI1 2),
     (forward_tac [hind RS Occ_ind_cond_Occ_domain] 1),
     (dres_inst_tac [("a", "Occ(?X)")] sym 1),
     (asm_simp_tac (nth_ss addsimps [[hcons, hind, hinv] MRS
				    def_Occinv_Occ,
				    Occ_Subtree_Nil]) 1),
     (asm_full_simp_tac (nth_ss addsimps [nth_map, length_map])  1),
     (etac RepFunE 1),
     (subgoals_tac ["nth(l, a): Terms"] 1),
     (forw_inst_tac [("M", "nth(l, a)")] 
      (hind RS Occ_ind_cond_Occ_domain) 1),
     (dtac subsetD 1),
     (atac 1),
     (etac SigmaE 1),
     (hyp_subst_tac 1),
     (asm_full_simp_tac nth_ss 1),
     (res_inst_tac [("a", "<Cons(a, xb), y>")] RepFun_eqI 1),
     (rtac Occ_consI2 2),
     (subgoals_tac ["a: nat",
		  "map(Occ, l): list(Pow(list(nat) * Tag))"] 1),
     (rtac map_type 2),
     (etac (hind RS Occ_ind_cond_Occ_domain RS PowI) 3),
     (etac mem_nat_in_nat 3),
     (atac 2),
     (rtac nth_type2 5),
     (REPEAT (CHANGED (asm_simp_tac (nth_ss addsimps [nth_map, length_map, 
						    Occ_subtree_Occ_cons,
						    Occ_Subtree_Cons]) 1)))]);

qed_goal "def_Sub_functional" SubOcc.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       !!M. Sub(M) == {<l, Occinv(Occ_Subtree(l, Occ(M)))>. <l, T>: Occ(M)}; \
\       Term_cons_inj_cond(Terms, Tag, Arity, Term_cons); \
\       M: Terms \
\    |] ==> functional(Sub(M))"
  (fn [hcons, hind, hinv, hsub, hinj, major] =>
    [(rtac ([hind, major] MRS Occ_ind_condD) 1),
     (asm_simp_tac (IFOL_ss addsimps 
		  [[hcons, hind, hinv, hsub, hinj] MRS def_Sub_rec]) 1),
     (rtac functionalI 1),
     (REPEAT (CHANGED (TRYALL (etac Occ_consE)))),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps [nth_map, length_map,
						  Cons_iff]))),
     (dtac bspec 3),
     (etac functionalD 4),
     (atac 4),
     (atac 3),
     (asm_simp_tac IFOL_ss 3),
     (ALLGOALS (fast_tac (ZF_cs addSEs list.free_SEs)))]);

qed_goal "def_subterm_Nil" SubOcc.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       !!M. Sub(M) == {<l, Occinv(Occ_Subtree(l, Occ(M)))>. <l, T>: Occ(M)}; \
\       Term_cons_inj_cond(Terms, Tag, Arity, Term_cons); \
\       !!M l. subterm(M, l) == THE N. <l, N>: Sub(M); \
\       M: Terms \
\    |] ==> subterm(M, []) = M"
  (fn [hcons, hind, hinv, hsub, hinj, hsubterm, major] =>
    [(rewrite_goals_tac [hsubterm]),
     (subgoals_tac ["<[], M>: Sub(M)"] 1),
     (rtac the_equality 1),
     (rtac ([hcons, hind, hinv, hsub, hinj, major] 
	  MRS def_Sub_functional RS functionalD) 2),
     (REPEAT (atac 1)),
     (rtac ([hind, major] MRS Occ_ind_condD) 1),
     (asm_simp_tac (IFOL_ss addsimps 
		  [[hcons, hind, hinv, hsub, hinj] MRS def_Sub_rec]) 1),
     (rtac Occ_consI1 1)]);

qed_goal "def_subterm_Cons" SubOcc.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       !!M. Sub(M) == {<l, Occinv(Occ_Subtree(l, Occ(M)))>. <l, T>: Occ(M)}; \
\       Term_cons_inj_cond(Terms, Tag, Arity, Term_cons); \
\       !!M l. subterm(M, l) == THE N. <l, N>: Sub(M); \
\       Term_cons(T, l): Terms; \
\       T: Tag; l: list(Terms); Arity(T) = length(l); \
\       m: list(nat); a: length(l) \
\    |] ==> subterm(Term_cons(T, l), Cons(a, m)) = subterm(nth(l, a), m)"
  (fn [hcons, hind, hinv, hsub, hinj, hsubterm, major, t_tag, l_list, 
     hlen, prem1, prem2] =>
    [(rewrite_goals_tac [hsubterm]),
     (cut_facts_tac [major, t_tag, l_list, hlen, prem1, prem2] 1),
     (asm_simp_tac (IFOL_ss addsimps 
		  [[hcons, hind, hinv, hsub, hinj] MRS def_Sub_rec]) 1),
     (subgoals_tac ["nth(l, a): Terms"] 1),
     (rtac nth_type2 2),
     (atac 2),
     (asm_simp_tac IFOL_ss 2),
     (res_inst_tac [("Q", "EX X. <m, X>: Sub(nth(l, a))")] 
    (excluded_middle RS disjE) 1),
     (rtac (the_0 RS sym RSN (2, trans)) 1),
     (rtac notI 2),
     (etac notE 2),
     (fast_tac ZF_cs 2),
     (rtac the_0 1),
     (rtac notI 1),
     (etac notE 1),
     (etac ex1E 1),
     (etac Occ_cons_ConsE 1),
     (rtac exI 1),
     (asm_full_simp_tac (nth_ss addsimps [nth_map, length_map]) 1),
     (rtac the_equality 1),
     (rtac (the_equality RS sym) 2),
     (etac Occ_cons_ConsE 3),
     (etac Occ_cons_ConsE 2),
     (rtac Occ_consI2 1),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps [nth_map, 
						  length_map]))),
     (rtac ([hcons, hind, hinv, hsub, hinj] MRS 
	  def_Sub_functional RS functionalD) 2),
     (REPEAT (atac 3)),
     (atac 2),
     (rtac theI 1),
     (etac exE 1),
     (rtac ex1I 1),
     (atac 1),
     (rtac ([hcons, hind, hinv, hsub, hinj] MRS 
	   def_Sub_functional RS functionalD) 1),
     (REPEAT (atac 2)),
     (atac 1)]);
