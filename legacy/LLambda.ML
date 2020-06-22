(*
    File:        LLambda.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open LLambda;

val LOcc_domain = LTermOcc.use_thm Occ_ind_cond_Occ_domain;
val LOcc_in_Occ_range = LTermOcc.use_thm Occ_ind_cond_Occ_in_Occ_range;

qed_goal "LOcc_typeD1" LLambda.thy
    "[| <l, T>: LOcc(M); M: LTerm |] ==> l: list(nat)"
  (fn [major,prem] =>
    [(rtac (major RS (prem RS LOcc_domain RS subsetD RS SigmaD1)) 1)]);

qed_goal "LOcc_typeD2" LLambda.thy
    "[| <l, T>: LOcc(M); M: LTerm |] ==> T: LTag"
  (fn [major,prem] =>
    [(rtac (major RS (prem RS LOcc_domain RS subsetD RS SigmaD2)) 1)]);

val LTerm_typeEs = map (fn s => prove_goal LLambda.thy s
                        (fn [major, prem] =>
                         [(rtac (major RS LTerm.elim) 1),
                          (ALLGOALS (fast_tac (ZF_cs addSEs LTerm.free_SEs 
                                               addIs [prem])))]))
    ["[| LVar(x): LTerm; x: LVariable ==> R |] ==> R",
     "[| LLam(x, M): LTerm; [| x: LVariable; M: LTerm |] ==> R |] ==> R",
     "[| LApp(M, N): LTerm; [| M: LTerm; N: LTerm |] ==> R |] ==> R"];

val LTag_typeEs = map (fn s => prove_goal LLambda.thy s
                        (fn [major, prem] =>
                         [(rtac (major RS LTermOcc.Tag.elim) 1),
                          (ALLGOALS (fast_tac (ZF_cs addSEs 
                                               LTermOcc.Tag.free_SEs 
                                               addIs [prem])))]))
    ["[| TLVar(x): LTag; x: LVariable ==> R |] ==> R",
     "[| TLLam(x): LTag; x: LVariable ==> R |] ==> R"];

val LTag_simps = map LTermOcc.Tag.mk_free
    ["TLVar(x) = TLVar(y) <-> x = y",
     "TLLam(x) = TLLam(y) <-> x = y"];

qed_goal "LOcc_LVarE" LLambda.thy
    "[| u: LOcc(LVar(x)); \
\       u = <[], TLVar(x)> ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Occ_eqns) 1),
     (etac Occ_consE 1),
     (etac prem 1),
     (asm_full_simp_tac (IFOL_ss addsimps [length_Nil]) 1),
     (etac emptyE 1)]);

qed_goal "LOcc_LLamE" LLambda.thy
    "[| u: LOcc(LLam(x, M)); \
\       u = <[], TLLam(x)> ==> R; \
\       !! l T. [| u = <Cons(0, l), T>; <l, T>: LOcc(M) |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2] =>
    [(cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Occ_eqns) 1),
     (etac Occ_consE 1),
     (etac prem1 1),
     (asm_full_simp_tac list_ss 1),
     (etac succE 1),
     (etac emptyE 2),
     (rtac prem2 1),
     (ALLGOALS (REPEAT o hyp_subst_tac)),
     (asm_full_simp_tac nth_ss 2),
     (rtac refl 1)]);

qed_goal "LOcc_LAppE" LLambda.thy
    "[| u: LOcc(LApp(M, N)); \
\       u = <[], TLApp> ==> R; \
\       !! l T. [| u = <Cons(0, l), T>; <l, T>: LOcc(M) |] ==> R; \
\       !! l T. [| u = <Cons(1, l), T>; <l, T>: LOcc(N) |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Occ_eqns) 1),
     (etac Occ_consE 1),
     (etac prem1 1),
     (asm_full_simp_tac list_ss 1),
     (etac succE 1),
     (etac succE 2),
     (etac emptyE 3),
     (rtac prem2 2),
     (rtac prem3 1),
     (ALLGOALS (REPEAT o hyp_subst_tac)),
     (TRYALL (rtac refl)),
     (ALLGOALS (asm_full_simp_tac nth_ss))]);

val LOcc_LTermEs = [LOcc_LVarE, LOcc_LLamE, LOcc_LAppE];

val LOcc_LTermIs = map (fn s => prove_goal LLambda.thy s
                         (fn prems =>
                          [(cut_facts_tac prems 1),
                           (asm_simp_tac 
                            (IFOL_ss addsimps LTermOcc.Occ_eqns) 1),
                           (resolve_tac [Occ_consI2, Occ_consI1] 1),
                           (IF_UNSOLVED (ALLGOALS (asm_simp_tac nth_ss))),
                           (IF_UNSOLVED (REPEAT 
                                         (ares_tac [succI1, succI2] 1)))]))
    ["<[], TLVar(x)>: LOcc(LVar(x))",
     "<[], TLLam(x)>: LOcc(LLam(x, M))",
     "<l, T>: LOcc(M) ==> <Cons(0, l), T>: LOcc(LLam(x, M))",
     "<l, T>: LOcc(M) ==> <Cons(0, l), T>: LOcc(LApp(M, N))",
     "<[], TLApp>: LOcc(LApp(M, N))",
     "<l, T>: LOcc(N) ==> <Cons(1, l), T>: LOcc(LApp(M, N))"];

(** LBinding **)
qed_goalw "LBindingI" LLambda.thy [LBinding_def]
    "[| M: LTerm; <l, TLLam(x)>: LOcc(M); <m, TLVar(x)>: LOcc(M); \
\       initseg(nat, l, m) \
\    |] ==> LBinding(<l, TLLam(x)>, <m, TLVar(x)>, M)"
  (fn prems =>
    [(REPEAT (ares_tac ([refl, conjI, exI] @ prems) 1))]);

qed_goalw "LBindingE" LLambda.thy [LBinding_def]
    "[| LBinding(v, u, M); \
\       !! x l m. [| v =  <l, TLLam(x)>; u = <m, TLVar(x)>; M: LTerm; \
\          <l, TLLam(x)>: LOcc(M); <m, TLVar(x)>: LOcc(M); \
\          initseg(nat, l, m) |] ==> R \
\    |] ==> R"
  (fn major::prems =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac [conjE, exE] 1)),
     (resolve_tac prems 1),
     (TRYALL atac),
     (ALLGOALS hyp_subst_tac),
     (REPEAT (atac 1))]);

qed_goal "LBindingE2" LLambda.thy
    "[| LBinding(<l, TLLam(x)>, <m, TLVar(x)>, M); \
\       [| M: LTerm; \
\          <l, TLLam(x)>: LOcc(M); <m, TLVar(x)>: LOcc(M); \
\          initseg(nat, l, m) |] ==> R \
\    |] ==> R"
  (fn major::prems =>
    [(rtac (major RS LBindingE) 1),
     (asm_full_simp_tac (ZF_ss addsimps LTag_simps) 1),
     (fast_tac (ZF_cs addIs prems) 1)]);

qed_goalw "LBindingD1" LLambda.thy [LBinding_def]
    "LBinding(v, u, M) ==> M: LTerm"
  (fn [major] =>
    [(rtac (major RS conjunct1) 1)]);

qed_goal "LBinding_LVarE" LLambda.thy
    "LBinding(v, u, LVar(x)) ==> R"
  (fn [major] =>
    [(rtac (major RS LBindingE) 1),
     (REPEAT (etac LOcc_LVarE 1)),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs) 1)]);

qed_goal "LBinding_LLamE" LLambda.thy
    "[| LBinding(v, u, LLam(x, N));\
\       !!l m. [| x: LVariable; N: LTerm; \
\           v = <[], TLLam(x)>; u = <Cons(0, m), TLVar(x)>;\
\          <m, TLVar(x)>: LOcc(N) |] ==> R; \
\       !!y l m. [| x: LVariable; N: LTerm; y: LVariable; \
\          v = <Cons(0, l), TLLam(y)>; u = <Cons(0, m), TLVar(y)>; \
\          LBinding(<l, TLLam(y)>, <m, TLVar(y)>, N) |] ==> R \
\   |] ==> R"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS LBindingE) 1),
     (REPEAT (ALLGOALS (etac LOcc_LLamE))),
     (TRYALL (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs))),
     (ALLGOALS ((REPEAT o (etac (Pair_iff RS iffD1 RS conjE))) THEN'
              (REPEAT o bound_hyp_subst_tac))),
     (asm_full_simp_tac (IFOL_ss addsimps [LTermOcc.Tag.mk_free 
                         "TLLam(x) = TLLam(y) <-> x = y"]) 1),
     (bound_hyp_subst_tac 1),
     (etac initseg_left_ConsE 2),
     (etac (Cons_iff RS iffD1 RS conjE) 2),
     (bound_hyp_subst_tac 2),
     (ALLGOALS (eresolve_tac LTerm_typeEs)),
     (forward_tac [LOcc_domain RS subsetD] 2),
     (atac 2),
     (dtac SigmaD2 2),
     (eresolve_tac LTag_typeEs 2),
     (rtac prem2 2),
     (atac 5),
     (rtac prem1 1),
     (REPEAT (ares_tac [LBindingI] 1))]);

qed_goal "LBinding_LAppE" LLambda.thy
    "[| LBinding(v, u, LApp(A, B));\
\       !!x l m. [| A: LTerm; B: LTerm; \
\          v = <Cons(0, l), TLLam(x)>; u = <Cons(0, m), TLVar(x)>; \
\          LBinding(<l, TLLam(x)>, <m, TLVar(x)>, A) |] ==> R; \
\       !!x l m. [| A: LTerm; B: LTerm; \
\          v = <Cons(1, l), TLLam(x)>; u = <Cons(1, m), TLVar(x)>; \
\          LBinding(<l, TLLam(x)>, <m, TLVar(x)>, B) |] ==> R \
\   |] ==> R"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS LBindingE) 1),
     (REPEAT (ALLGOALS (etac LOcc_LAppE))),
     (TRYALL (fast_tac (FOL_cs addSEs LTermOcc.Tag.free_SEs))),
     (ALLGOALS ((REPEAT o (etac (Pair_iff RS iffD1 RS conjE))) THEN'
              (REPEAT o bound_hyp_subst_tac))),
     (ALLGOALS ((etac initseg_left_ConsE) THEN'
              (etac (Cons_iff RS iffD1 RS conjE)) THEN'
              bound_hyp_subst_tac)),
     (TRYALL (eresolve_tac [succ_neq_0, sym RS succ_neq_0])),
     (ALLGOALS (eresolve_tac LTerm_typeEs)),
     (rtac prem2 2),
     (rtac prem1 1),
     (REPEAT (ares_tac [LBindingI] 1))]);

val LBinding_LTermEs = [LBinding_LVarE, LBinding_LLamE, LBinding_LAppE];

(** LBoundBy **)
qed_goalw "LBoundByI2" LLambda.thy [LBoundBy_def]
    "greatest(initseg(nat), \
\            {n:list(nat). EX T. LBinding(<n, T>, <m, TLVar(x)>, M)}, l)\
\      ==> LBoundBy(<m, TLVar(x)>, <l, TLLam(x)>, M)"
  (fn [prem1] =>
    [(cut_facts_tac [prem1 RS greatestD1] 1),
     (safe_tac ZF_cs),
     ((rtac LBindingE 1) THEN atac 1),
     (rtac (exI RS exI RS exI) 1),
     (safe_tac ZF_cs),
     (REPEAT (ares_tac [refl, greatestI, prem1 RS greatestD2,
		      CollectI, exI] 1))]);

qed_goal "LBoundByI" LLambda.thy
    "[| LBinding(<l, TLLam(x)>, <m, TLVar(x)>, M); \
\       !! n. [| <n, TLLam(x)>: LOcc(M); \
\          LBinding(<n, TLLam(x)>, <m, TLVar(x)>, M); \
\          initseg(nat, l, n) |] ==> n = l \
\    |] ==> LBoundBy(<m, TLVar(x)>, <l, TLLam(x)>, M)"
  (fn [prem1, prem2] =>
    [(rtac LBoundByI2 1),
     (rtac greatestI 1),
     (rtac (prem1 RS LBindingE2) 2),
     (forward_tac [initsegD1] 2),
     (fast_tac (ZF_cs addIs [LBindingI]) 2),
     (safe_tac ZF_cs),
     ((rtac LBindingE 1) THEN (atac 1)),
     (cut_facts_tac [prem1] 1),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs)),
     (res_inst_tac [("x1", "l"), ("y1", "la")] (chainD2 RS disjE) 1),
     (etac (initsegD2 RS initseg_downset_forms_a_chain) 1),
     (fast_tac (ZF_cs addSEs [LBindingE] addIs [downsetI]
		addDs [initsegD1, initsegD2]) 1),
     (fast_tac (ZF_cs addSEs [LBindingE] addIs [downsetI]
		addDs [initsegD1, initsegD2]) 1),
     (dtac prem2 1),
     (hyp_subst_tac 3),
     (REPEAT (atac 1))]);

qed_goalw "LBoundByD1" LLambda.thy [LBoundBy_def]
    "LBoundBy(u, v, M) ==> LBinding(v, u, M)"
  (fn [major] =>
    [(cut_facts_tac [major] 1),
     (safe_tac ZF_cs),
     (dtac greatestD1 1),
     (fast_tac (ZF_cs addEs [LBindingE] addSEs LTermOcc.Tag.free_SEs
		addIs [LBindingI]) 1)]);

qed_goal "LBoundByE" LLambda.thy
    "[| LBoundBy(u, v, M); \
\       !! x l m. [| u = <l, TLVar(x)>; v = <m, TLLam(x)>; \
\          LBinding(<m, TLLam(x)>, <l, TLVar(x)>, M); \
\          ALL n. initseg(nat, m, n) --> \
\                 LBinding(<n, TLLam(x)>, <l, TLVar(x)>, M) --> n = m\
\       |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major, major RS LBoundByD1] 1),
     (rewrite_goals_tac [LBoundBy_def]),
     (REPEAT (eresolve_tac [exE, conjE] 1)),
     (rtac prem 1),
     (hyp_subst_tac 3),
     (REPEAT (atac 1)),
     (safe_tac ZF_cs),
     ((rtac (greatest_unique RS sym) 1) THEN (atac 1)),
     (rtac greatestI 1),
     ((rtac initseg_trans 1) THEN (atac 2)),
     (etac greatestD2 1),
     (atac 1),
     (fast_tac (ZF_cs addEs [initsegD2]) 1),
     (rtac ([Collect_subset, poset_initseg] MRS poset_subset) 1)]);

qed_goal "LBoundByE2" LLambda.thy
    "[| LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, M); \
\       [| LBinding(<m, TLLam(x)>, <l, TLVar(x)>, M); \
\          ALL n. initseg(nat, m, n) --> \
\                 LBinding(<n, TLLam(x)>, <l, TLVar(x)>, M) --> n = m\
\       |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS LBoundByE) 1),
     (asm_full_simp_tac (ZF_ss addsimps LTag_simps) 1),
     (etac conjE 1),
     (REPEAT (bound_hyp_subst_tac 1)),
     (REPEAT (ares_tac [prem] 1))]);



qed_goal "LBinding_imp_LBoundBy_lemma" LLambda.thy
    "LBinding(v, u, M) ==> EX w. LBoundBy(u, w, M)"
  (fn [major] =>
    [(cut_facts_tac [major] 1),
     ((rtac LBindingE 1) THEN (atac 1)),
     (hyp_subst_tac 1),
     (subgoal_tac "{n: list(nat). EX T. LBinding(<n, T>, <m, TLVar(x)>, M)} \
\                  <= downset(initseg(nat), list(nat), m)" 1),
     (fast_tac (ZF_cs addSEs [LBindingE] addIs [downsetI]) 2),
     (res_inst_tac [("P1", "{n: list(nat). EX T. LBinding(<n, T>, <m, TLVar(x)>, M)}")]
      (Finite_non_empty_chain_has_greatest_element RS exE) 1),
     (rtac subset_Finite 1),
     (atac 1),
     (etac (initsegD2 RS initseg_downset_is_Finite) 1),
     (etac chain_subset 1),
     (etac (initsegD2 RS initseg_downset_forms_a_chain) 1),
     (rtac (CollectI RS not_emptyI) 1),
     (etac exI 2),
     (etac initsegD1 1),
     (rtac exI 1),
     (etac LBoundByI2 1)]);

qed_goal "LBinding_imp_LBoundBy" LLambda.thy
    "LBinding(v, u, M) ==> EX! w. LBoundBy(u, w, M)"
  (fn [major] =>
    [(cut_facts_tac [major RS LBinding_imp_LBoundBy_lemma] 1),
     (etac exE 1),
     ((rtac ex1I 1) THEN (atac 1)),
     (rewrite_goals_tac [LBoundBy_def]),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs)),
     ((dtac greatest_unique 1) THEN (atac 1)),
     (rtac ([Collect_subset, poset_initseg] MRS poset_subset) 1),
     (asm_simp_tac IFOL_ss 1)]);

qed_goal "LBoundByE3" LLambda.thy
    "[| LBoundBy(u, v, M); \
\       [| LBinding(v, u, M); \
\          ALL w. LBoundBy(u, w, M) --> w = v |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major RS LBoundByD1] 1),
     (etac (LBinding_imp_LBoundBy RS ex1E) 1),
     (forward_tac [spec RS mp] 1),
     (rtac major 1),
     (bound_hyp_subst_tac 1),
     (dtac LBoundByD1 1),
     (REPEAT (ares_tac [prem] 1))]);

qed_goal "LBinding_imp_LBoundByE" LLambda.thy
    "[| LBinding(v, <l, TLVar(x)>, M); \
\       !!m. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, M) ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS LBinding_imp_LBoundBy RS ex1E) 1),
     (etac LBoundByE 1),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs)),
     (rtac prem 1),
     (rtac LBoundByI 1),
     (atac 1),
     (etac (spec RS mp RS mp) 1),
     (REPEAT (atac 1))]);

qed_goalw "LBoundInI" LLambda.thy [LBoundIn_def]
    "EX v. LBinding(v, u, M) ==> LBoundIn(u, M)"
  (fn [prem] =>
    [(rtac (prem RS exE) 1),
     (etac LBindingE 1),
     (fast_tac ZF_cs 1)]);

qed_goalw "LBoundInE" LLambda.thy [LBoundIn_def]
    "[| LBoundIn(u, M); !!v. LBinding(v, u, M) ==> R |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac [exE, conjE, bexE] 1)),
     (rtac prem 1),
     (REPEAT (hyp_subst_tac 1)),
     (REPEAT (ares_tac [LBindingI] 1))]);

(** LFreeIn **)
qed_goalw "LFreeInI" LLambda.thy [LFreeIn_def]
    "[| M: LTerm; <m, TLVar(x)>: LOcc(M); \
\       !! l. [| <l, TLLam(x)>: LOcc(M);  initseg(nat, l, m) |] ==> False \
\    |] ==> LFreeIn(<m, TLVar(x)>, M)"
  (fn [prem1, prem2, prem3] =>
    [(REPEAT (ares_tac [prem1, prem2, refl, conjI, exI, notI] 1)),
     (REPEAT (eresolve_tac [bexE, exE, conjE] 1)),
     (bound_hyp_subst_tac 1),
     (REPEAT (ares_tac [prem3] 1))]);

qed_goal "LFreeInI2" LLambda.thy
    "[| M: LTerm; <m, TLVar(x)>: LOcc(M); \
\       !! l. LBinding(<l, TLLam(x)>, <m, TLVar(x)>, M) ==> False \
\    |] ==> LFreeIn(<m, TLVar(x)>, M)"
  (fn [prem1, prem2, prem3] =>
    [(rtac ([prem1, prem2] MRS LFreeInI) 1),
     (rtac prem3 1),
     (REPEAT (ares_tac [prem1, prem2, LBindingI] 1))]);

qed_goalw "LFreeInD1" LLambda.thy [LFreeIn_def]
    "LFreeIn(u, M) ==> M: LTerm"
  (fn [prem] =>
    [(rtac (prem RS conjunct1) 1)]);

qed_goalw "LFreeInE" LLambda.thy [LFreeIn_def]
    "[| LFreeIn(u, M); \
\       !! l x. [| M: LTerm; u = <l, TLVar(x)>; <l, TLVar(x)>: LOcc(M); \
\                 ALL m. <m, TLLam(x)>: LOcc(M) --> ~initseg(nat, m, l) \
\       |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac [conjE, exE] 1)),
     (rtac prem 1),
     (hyp_subst_tac 3),
     (REPEAT (atac 1)),
     (rtac (notI RS impI RS allI) 1),
     (etac notE 1),
     (REPEAT (ares_tac [bexI, exI, refl, conjI] 1))]);

qed_goal "LFreeInE2" LLambda.thy
    "[| LFreeIn(<l, TLVar(x)>, M); \
\       [| M: LTerm; <l, TLVar(x)>: LOcc(M); \
\                 ALL m. <m, TLLam(x)>: LOcc(M) --> ~initseg(nat, m, l) \
\       |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS LFreeInE) 1),
     (asm_full_simp_tac (ZF_ss addsimps LTag_simps) 1),
     (etac conjE 1),
     (bound_hyp_subst_tac 1),
     (REPEAT (ares_tac [prem] 1))]);

qed_goal "LFreeIn_LVarI" LLambda.thy
    "x: LVariable ==> LFreeIn(<[], TLVar(x)>, LVar(x))"
  (fn [major] =>
    [(rtac LFreeInI2 1),
     (eresolve_tac LBinding_LTermEs 3),
     (REPEAT (ares_tac (LTerm.intrs @ LOcc_LTermIs @ [major]) 1))]);

qed_goal "LFreeIn_LLamI" LLambda.thy
    "[| LFreeIn(<l, TLVar(x)>, M); x ~= y; y: LVariable |] ==> \
\            LFreeIn(<Cons(0, l), TLVar(x)>, LLam(y, M))"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS LFreeInE) 1),
     (rtac LFreeInI2 1),
     (eresolve_tac LBinding_LTermEs 3),
     (rtac (prem1 RS notE) 3),
     (REPEAT (ares_tac ([prem1, prem2] @ LTerm.intrs @ LOcc_LTermIs) 1)),
     (safe_tac (ZF_cs addSEs list.free_SEs addSEs LTermOcc.Tag.free_SEs)),
     (etac LBindingE2 1),
     (etac (spec RS mp RS notE) 1),
     (REPEAT (atac 1))]);

qed_goal "LFreeIn_LAppI1" LLambda.thy
    "[| LFreeIn(<l, T>, M); N: LTerm |] ==> \
\            LFreeIn(<Cons(0, l), T>, LApp(M, N))"
  (fn [major, prem] =>
    [(rtac (major RS LFreeInE) 1),
     (safe_tac ZF_cs),
     (rtac LFreeInI2 1),
     (eresolve_tac LBinding_LTermEs 3),
     (fast_tac (ZF_cs addSEs list.free_SEs) 4),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs list.free_SEs 
                           addSEs LTermOcc.Tag.free_SEs
                           addSEs [LBindingE2])) 3),
     (etac (spec RS mp RS notE) 3),
     (REPEAT (ares_tac ([prem] @ LTerm.intrs @ LOcc_LTermIs) 1))]);

qed_goal "LFreeIn_LAppI2" LLambda.thy
    "[| LFreeIn(<l, T>, N); M: LTerm |] ==> \
\            LFreeIn(<Cons(1, l), T>, LApp(M, N))"
  (fn [major, prem] =>
    [(rtac (major RS LFreeInE) 1),
     (safe_tac ZF_cs),
     (rtac LFreeInI2 1),
     (eresolve_tac LBinding_LTermEs 3),
     (fast_tac (ZF_cs addSEs list.free_SEs) 3),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs list.free_SEs 
                           addSEs LTermOcc.Tag.free_SEs
                           addSEs [LBindingE2])) 3),
     (etac (spec RS mp RS notE) 3),
     (REPEAT (ares_tac ([prem] @ LTerm.intrs @ LOcc_LTermIs) 1))]);

val LFreeIn_LTermIs = [LFreeIn_LVarI, LFreeIn_LLamI, 
                       LFreeIn_LAppI1, LFreeIn_LAppI2];

qed_goal "LFreeIn_LVarE" LLambda.thy
    "[| LFreeIn(u, LVar(x)); \
\       [| u = <[], TLVar(x)>; x: LVariable |] ==> R\
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS LFreeInE) 1),
     (eresolve_tac LOcc_LTermEs 1),
     (eresolve_tac LTerm_typeEs 1),
     (rtac prem 1),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs))]);

qed_goal "LFreeIn_LLamE" LLambda.thy
    "[| LFreeIn(u, LLam(x, M)); \
\       !!l y. [| u = <Cons(0, l), TLVar(y)>; x ~= y; x: LVariable; \
\         LFreeIn(<l, TLVar(y)>, M) |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS LFreeInE) 1),
     (eresolve_tac LOcc_LTermEs 1),
     (eresolve_tac LTerm_typeEs 2),
     (rtac prem 2),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs)),
     (rtac refl 1),
     (etac (spec RS mp RS notE) 1),
     (rtac initseg_NilI 2),
     (dtac (LOcc_domain RS subsetD RS SigmaD1) 2),
     (rtac LFreeInI 4),
     (etac (spec RS mp RS notE) 6),
     (rtac initseg_ConsI 7),
     (REPEAT (ares_tac (list.intrs @ LOcc_LTermIs @ [nat_0I]) 1))]);

qed_goal "LFreeIn_LAppE" LLambda.thy
    "[| LFreeIn(u, LApp(M, N)); \
\       !!l x. [| u = <Cons(0, l), TLVar(x)>; N: LTerm; \
\         LFreeIn(<l, TLVar(x)>, M) |] ==> R; \
\       !!l x. [| u = <Cons(1, l), TLVar(x)>; M: LTerm; \
\         LFreeIn(<l, TLVar(x)>, N) |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS LFreeInE) 1),
     (eresolve_tac LOcc_LTermEs 1),
     (rtac prem2 3),
     (rtac prem1 2),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs LTerm_typeEs)),
     (TRYALL (rtac refl)),
     (ALLGOALS (rtac LFreeInI)),
     (etac (spec RS mp RS notE) 6),
     (etac (spec RS mp RS notE) 3),
     (rtac initseg_ConsI 8),
     (rtac initseg_ConsI 4),
     (REPEAT (ares_tac (list.intrs @ LOcc_LTermIs @ [nat_0I, nat_1I]) 1))]);

val LFreeIn_LTermEs = [LFreeIn_LVarE, LFreeIn_LLamE, LFreeIn_LAppE];


(** LBoundBy_LTerm **)
val LBoundBy_LVarE = standard (LBoundByD1 RS LBinding_LVarE);

qed_goal "LBoundBy_LLamE" LLambda.thy
    "[| LBoundBy(u, v, LLam(x, N));\
\       !!l m. [| x: LVariable; N: LTerm; \
\           v = <[], TLLam(x)>; u = <Cons(0, m), TLVar(x)>;\
\           LFreeIn(<m, TLVar(x)>, N) |] ==> R; \
\       !!y l m. [| x: LVariable; N: LTerm; y: LVariable; \
\          v = <Cons(0, l), TLLam(y)>; u = <Cons(0, m), TLVar(y)>; \
\          LBoundBy(<m, TLVar(y)>, <l, TLLam(y)>, N) |] ==> R \
\   |] ==> R"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS LBoundByD1 RS LBinding_LLamE) 1),
     (rtac prem2 2),
     (rtac prem1 1),
     (rtac LFreeInI2 5),
     (REPEAT (atac 1)),
     (atac 5),
     (REPEAT (atac 2)),
     (ALLGOALS (cut_facts_tac [major])),
     (ALLGOALS hyp_subst_tac),
     (ALLGOALS (etac LBoundByE2)),
     (REPEAT (etac LBindingE2 1)),
     (dtac (spec RS mp RS mp) 1),
     (rtac LBindingI 2),
     (rtac initseg_ConsI 5),
     (atac 6),
     (rtac initseg_NilI 1),
     (resolve_tac list.intrs 1),
     (etac initsegD1 2),
     (simp_tac (IFOL_ss addsimps LTermOcc.Occ_eqns) 3),
     (rtac Occ_consI2 3),
     (asm_simp_tac nth_ss 4),
     (asm_simp_tac list_ss 3),
     (fast_tac (ZF_cs addSEs list.free_SEs) 5),
     (REPEAT (ares_tac [nat_0I] 1)),
     (rtac LBoundByI 1),
     (atac 1),
     (dtac (spec RS mp RS mp) 1),
     (rtac initseg_ConsI 1),
     (atac 2),
     (etac (Cons_iff RS iffD1 RS conjunct2) 3),
     (REPEAT (etac LBindingE2 2)),
     (rtac LBindingI 2),
     (simp_tac (IFOL_ss addsimps LTermOcc.Occ_eqns) 3),
     (rtac Occ_consI2 3),
     (asm_simp_tac nth_ss 4),
     (asm_simp_tac list_ss 3),
     (REPEAT (ares_tac [nat_0I, initseg_ConsI, LBindingI] 1))]);

qed_goal "LBoundBy_LAppE" LLambda.thy
    "[| LBoundBy(u, v, LApp(A, B));\
\       !!x l m. [| A: LTerm; B: LTerm; \
\          v = <Cons(0, l), TLLam(x)>; u = <Cons(0, m), TLVar(x)>; \
\          LBoundBy(<m, TLVar(x)>, <l, TLLam(x)>, A) |] ==> R; \
\       !!x l m. [| A: LTerm; B: LTerm; \
\          v = <Cons(1, l), TLLam(x)>; u = <Cons(1, m), TLVar(x)>; \
\          LBoundBy(<m, TLVar(x)>, <l, TLLam(x)>, B) |] ==> R \
\   |] ==> R"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS LBoundByD1 RS LBinding_LAppE) 1),
     (rtac prem2 2),
     (rtac prem1 1),
     (REPEAT (atac 1)),
     (REPEAT (atac 2)),
     (ALLGOALS (cut_facts_tac [major])),
     (ALLGOALS hyp_subst_tac),
     (ALLGOALS (etac LBoundByE2)),
     (ALLGOALS ((rtac LBoundByI) THEN' atac)),
     (ALLGOALS (dtac (spec RS mp RS mp))),
     (TRYALL (etac (Cons_iff RS iffD1 RS conjunct2))),
     (TRYALL ((rtac initseg_ConsI) THEN'
              (REPEAT o (ares_tac [nat_0I, nat_succI])))),
     (ALLGOALS (REPEAT o (etac LBindingE2))),
     (ALLGOALS (rtac LBindingI)),
     (TRYALL atac),
     (TRYALL ((rtac initseg_ConsI) THEN'
              (REPEAT o (ares_tac [nat_0I, nat_succI])))),
     (ALLGOALS (simp_tac (IFOL_ss addsimps LTermOcc.Occ_eqns))),
     (ALLGOALS (rtac Occ_consI2)),
     (ALLGOALS (asm_simp_tac nth_ss)),
     (REPEAT (ares_tac [succI1, succI2] 1))]);

val LBoundBy_LTermEs = [LBoundBy_LVarE, LBoundBy_LLamE, LBoundBy_LAppE];

qed_goal "LBoundBy_LLamI1" LLambda.thy
    "LFreeIn(<l, TLVar(x)>, M) ==> \
\          LBoundBy(<Cons(0, l), TLVar(x)>, <[], TLLam(x)>, LLam(x, M))"
  (fn [major] =>
    [(rtac (major RS LFreeInE2) 1),
     (rtac LBoundByI 1),
     (rtac LBindingI 1),
     (resolve_tac LTerm.intrs 1),
     (dtac (LOcc_domain RS subsetD RS SigmaD2) 1),
     (atac 1),
     (eresolve_tac LTag_typeEs 1),
     (REPEAT (ares_tac (LOcc_LTermIs @ list.intrs @ [initseg_NilI, nat_0I]) 1)),
     (etac (LOcc_domain RS subsetD RS SigmaD1) 1),
     (atac 1),
     (eresolve_tac LOcc_LTermEs 1),
     (fast_tac ZF_cs 1),
     (safe_tac (ZF_cs addSEs LBinding_LTermEs 
              addSEs list.free_SEs addSEs LTermOcc.Tag.free_SEs)),
     (etac LBindingE2 1),
     (etac (spec RS mp RS notE) 1),
     (REPEAT (atac 1))]);

qed_goal "LBoundBy_LLamI2" LLambda.thy
    "[| LBoundBy(<l, T>, <m, U>, M);  x: LVariable |] ==> \
\          LBoundBy(<Cons(0, l), T>, <Cons(0, m), U>, LLam(x, M))"
  (fn [major, prem] =>
    [(rtac (major RS LBoundByE) 1),
     (safe_tac ZF_cs),
     (rtac LBoundByI 1),
     (eresolve_tac LBinding_LTermEs 2),
     (TRYALL (etac initseg_left_ConsE)),
     (hyp_subst_tac 2),
     (safe_tac (ZF_cs addSEs list.free_SEs addSEs LTermOcc.Tag.free_SEs)),
     (dtac (spec RS mp RS mp) 2),
     (etac LBindingE2 1),
     (rtac LBindingI 1),
     (REPEAT (ares_tac (LTerm.intrs @ LOcc_LTermIs @ 
                      [initseg_ConsI, nat_0I, prem]) 1)),
     (hyp_subst_tac 1),
     (rtac refl 1)]);

qed_goal "LBoundBy_LAppI1" LLambda.thy
    "[| LBoundBy(<l, T>, <m, U>, M); N: LTerm |] ==> \
\      LBoundBy(<Cons(0, l), T>, <Cons(0, m), U>, LApp(M, N))"
  (fn [major, prem] =>
    [(rtac (major RS LBoundByE) 1),
     (safe_tac ZF_cs),
     (rtac LBoundByI 1),
     (eresolve_tac LBinding_LTermEs 2),
     (etac initseg_left_ConsE 2),
     (safe_tac (ZF_cs addSEs list.free_SEs addSEs LTermOcc.Tag.free_SEs)),
     (dtac (spec RS mp RS mp) 2),
     (etac LBindingE2 1),
     (rtac LBindingI 1),
     (REPEAT (ares_tac (LTerm.intrs @ LOcc_LTermIs @ 
                      [initseg_ConsI, nat_0I, prem]) 1)),
     (hyp_subst_tac 1),
     (rtac refl 1)]);

qed_goal "LBoundBy_LAppI2" LLambda.thy
    "[| LBoundBy(<l, T>, <m, U>, N); M: LTerm |] ==> \
\      LBoundBy(<Cons(1, l), T>, <Cons(1, m), U>, LApp(M, N))"
  (fn [major, prem] =>
    [(rtac (major RS LBoundByE) 1),
     (safe_tac ZF_cs),
     (rtac LBoundByI 1),
     (eresolve_tac LBinding_LTermEs 2),
     (etac initseg_left_ConsE 3),
     (safe_tac (ZF_cs addSEs list.free_SEs addSEs LTermOcc.Tag.free_SEs)),
     (dtac (spec RS mp RS mp) 2),
     (etac LBindingE2 1),
     (rtac LBindingI 1),
     (REPEAT (ares_tac (LTerm.intrs @ LOcc_LTermIs @ 
                      [initseg_ConsI, nat_1I, prem]) 1)),
     (hyp_subst_tac 1),
     (rtac refl 1)]);

val LBoundBy_LTermIs = [LBoundBy_LLamI1, LBoundBy_LLamI2,
                        LBoundBy_LAppI1, LBoundBy_LAppI2];


(** LFV **)
qed_goalw "LFV_I" LLambda.thy [LFV_def]
    "LFreeIn(<l, TLVar(x)>, M) ==> x: LFV(M)"
  (fn [prem] =>
    [(rtac (prem RS LFreeInE2) 1),
     (dtac (LOcc_domain RS subsetD) 1),
     (atac 1),
     (etac SigmaE2 1),
     (eresolve_tac LTag_typeEs 1),
     (REPEAT (ares_tac [CollectI, prem, exI] 1))]);

qed_goalw "LFV_E" LLambda.thy [LFV_def]
    "[| x: LFV(M); !!l. LFreeIn(<l, TLVar(x)>, M) ==> R |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS CollectE) 1),
     (fast_tac (ZF_cs addIs [prem]) 1)]);

qed_goalw "LFV_LVar" LLambda.thy [LFV_def]
    "x: LVariable ==> LFV(LVar(x)) = {x}"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [LFreeInE] addSEs LTerm_typeEs
              addSEs LOcc_LTermEs addSEs LTermOcc.Tag.free_SEs)),
     (rtac exI 1),
     (rtac LFreeInI 1),
     (eresolve_tac LOcc_LTermEs 3),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs) 3),
     (REPEAT (ares_tac (LTerm.intrs @ LOcc_LTermIs) 1))]);

qed_goalw "LFV_LLam" LLambda.thy [LFV_def]
    "x: LVariable ==> LFV(LLam(x, N)) = LFV(N) - {x}"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [LFreeInE] addSEs LTerm_typeEs
              addSEs LOcc_LTermEs addSEs LTermOcc.Tag.free_SEs)),
     (etac (spec RS mp RS notE) 2),
     (rtac initseg_NilI 3),
     (dtac (LOcc_domain RS subsetD) 3),
     (resolve_tac list.intrs 4),
     (etac SigmaD1 5),
     (REPEAT (ares_tac ([nat_0I] @ LOcc_LTermIs) 2)),
     (ALLGOALS (rtac exI)),
     (ALLGOALS (rtac LFreeInI2)),
     (TRYALL (atac ORELSE'
            (eresolve_tac LOcc_LTermIs) ORELSE'
            ((eresolve_tac LTerm.intrs) THEN' atac))),
     (eresolve_tac LBinding_LTermEs 2),
     (safe_tac (ZF_cs addSEs [LBindingE2]
              addSEs LTermOcc.Tag.free_SEs addSEs list.free_SEs)),
     (ALLGOALS (etac (spec RS mp RS notE))),
     (rtac initseg_ConsI 2),
     (REPEAT (ares_tac ([nat_0I] @ LOcc_LTermIs) 1))]);

qed_goalw "LFV_LApp" LLambda.thy [LFV_def]
    "[| M: LTerm; N: LTerm |] ==> LFV(LApp(M, N)) = LFV(M) Un LFV(N)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [LFreeInE] addSEs LTerm_typeEs
              addSEs LOcc_LTermEs addSEs LTermOcc.Tag.free_SEs)),
     (etac notE 2),
     (ALLGOALS (rtac exI)),
     (ALLGOALS (rtac LFreeInI2)),
     (TRYALL (atac ORELSE'
            (eresolve_tac LOcc_LTermIs) ORELSE'
            ((eresolve_tac LTerm.intrs) THEN' atac))),
     (TRYALL (eresolve_tac LBinding_LTermEs)),
     (safe_tac (ZF_cs addSEs [LBindingE2]
              addSEs LTermOcc.Tag.free_SEs addSEs list.free_SEs)),
     (ALLGOALS (etac (spec RS mp RS notE))),
     (rtac initseg_ConsI 4),
     (rtac initseg_ConsI 2),
     (REPEAT (ares_tac ([nat_0I, nat_succI] @ LOcc_LTermIs) 1))]);


(** LFO **)
qed_goalw "LFO_I" LLambda.thy [LFO_def]
    "LFreeIn(<l, TLVar(x)>, M) ==> <l, TLVar(x)>: LFO(x, M)"
  (fn [prem] =>
    [(rtac (prem RS LFreeInE2) 1),
     (dtac (LOcc_domain RS subsetD) 1),
     (atac 1),
     (REPEAT (ares_tac [CollectI, prem, exI, conjI, refl] 1))]);

qed_goalw "LFO_E" LLambda.thy [LFO_def]
    "[| u: LFO(x, M); \
\      !!l. [| u = <l, TLVar(x)>; LFreeIn(<l, TLVar(x)>, M) |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS CollectE) 1),
     (REPEAT (eresolve_tac [exE, conjE] 1)),
     (rtac prem 1),
     (hyp_subst_tac 2),
     (REPEAT (atac 1))]);

qed_goal "LFO_E2" LLambda.thy
    "[| <l, TLVar(y)>: LFO(x, M); \
\      [| y = x; LFreeIn(<l, TLVar(x)>, M) |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS LFO_E) 1),
     (asm_full_simp_tac (ZF_ss addsimps LTag_simps) 1),
     (rtac prem 1),
     (etac conjunct2 1),
     (asm_simp_tac IFOL_ss 1)]);

qed_goalw "LFO_LVar1" LLambda.thy [LFO_def]
    "x: LVariable ==> LFO(x, LVar(x)) = {<[], TLVar(x)>}"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [LFreeInE] addSEs LTerm_typeEs
              addSEs LOcc_LTermEs addSEs LTermOcc.Tag.free_SEs)),
     (REPEAT (ares_tac (list.intrs @ LTermOcc.Tag.intrs 
                      @ [exI, refl, conjI]) 1)),
     (rtac LFreeInI 1),
     (eresolve_tac LOcc_LTermEs 3),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs) 3),
     (REPEAT (ares_tac (LTerm.intrs @ LOcc_LTermIs) 1))]);

qed_goalw "LFO_LVar2" LLambda.thy [LFO_def]
    "x ~= y ==> LFO(x, LVar(y)) = 0"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [LFreeInE] addSEs LTerm_typeEs
              addSEs LOcc_LTermEs addSEs LTermOcc.Tag.free_SEs))]);

qed_goalw "LFO_LLam1" LLambda.thy [LFO_def]
    "LFO(x, LLam(x, M)) = 0"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [LFreeInE, ConsE] addSEs LTerm_typeEs
              addSEs LOcc_LTermEs addSEs LTermOcc.Tag.free_SEs)),
     (etac (spec RS mp RS notE) 1),
     (rtac initseg_NilI 2),
     (REPEAT (ares_tac (list.intrs @ LOcc_LTermIs) 1))]);

qed_goalw "LFO_LLam2" LLambda.thy [LFO_def]
    "[| x ~= y; y: LVariable |] \
\       ==> LFO(x, LLam(y, M)) = Occ_shift(0, LFO(x, M))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [LFreeInE, ConsE, Occ_shiftE] addSEs LTerm_typeEs
              addSEs LOcc_LTermEs addSEs LTermOcc.Tag.free_SEs
              addSIs [Occ_shiftI])),
     (REPEAT (ares_tac (list.intrs @ [nat_0I, nat_succI]) 2)),
     (ALLGOALS (REPEAT o (resolve_tac [exI, conjI, refl]))),
     (ALLGOALS (rtac LFreeInI2)),
     (TRYALL (atac ORELSE'
            (eresolve_tac LOcc_LTermIs) ORELSE'
            ((eresolve_tac LTerm.intrs) THEN' atac))),
     (eresolve_tac LBinding_LTermEs 2),
     (safe_tac (ZF_cs addSEs [LBindingE2]
              addSEs LTermOcc.Tag.free_SEs addSEs list.free_SEs)),
     (ALLGOALS (etac (spec RS mp RS notE))),
     (rtac initseg_ConsI 2),
     (REPEAT (ares_tac ([nat_0I, nat_succI] @ LOcc_LTermIs) 1))]);

qed_goalw "LFO_LApp" LLambda.thy [LFO_def]
    "[| M: LTerm; N: LTerm |] ==> \
\    LFO(x, LApp(M, N)) = Occ_shift(0, LFO(x, M)) Un Occ_shift(1, LFO(x, N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [LFreeInE, Occ_shiftE, ConsE] addSEs LTerm_typeEs
              addSEs LOcc_LTermEs addSEs LTermOcc.Tag.free_SEs
              addSIs [Occ_shiftI])),
     (TRYALL (REPEAT o (ares_tac (list.intrs @ [nat_0I, nat_succI])))),
     (ALLGOALS (REPEAT o (resolve_tac [exI, conjI, refl]))),
     (ALLGOALS (rtac LFreeInI2)),
     (TRYALL (atac ORELSE'
            (eresolve_tac LOcc_LTermIs) ORELSE'
            ((eresolve_tac LTerm.intrs) THEN' atac))),
     (TRYALL (eresolve_tac LBinding_LTermEs)),
     (safe_tac (ZF_cs addSEs [LBindingE2]
              addSEs LTermOcc.Tag.free_SEs addSEs list.free_SEs)),
     (ALLGOALS (etac (spec RS mp RS notE))),
     (rtac initseg_ConsI 4),
     (rtac initseg_ConsI 2),
     (REPEAT (ares_tac ([nat_0I, nat_succI] @ LOcc_LTermIs) 1))]);

val LFV_eqns = [LFV_LVar, LFV_LLam, LFV_LApp];
val LFO_eqns = [LFO_LVar1, LFO_LVar2, LFO_LLam1, LFO_LLam2, LFO_LApp];


(** Lsubst **)
qed_goalw "LFO_subset_LOcc" LLambda.thy [LFO_def]
    "LFO(x, M) <= LOcc(M)"
  (fn _ =>
    [(fast_tac (ZF_cs addSEs [LFreeInE] addSEs LTermOcc.Tag.free_SEs) 1)]);

qed_goalw "Incomparable_LFO" LLambda.thy [LFO_def]
    "M: LTerm ==> Incomparable(domain(LFO(x, M)))"
  (fn [prem] =>
    [(rtac Incomparable_subset 1),
     (rtac Incomparable_CorrectArity_0 1),
     (rtac (prem RS (LOcc_domain)) 1),
     (rtac (prem RS LOcc_in_Occ_range RS Occ_range_DenseTreeD) 1),
     (rtac domain_mono 1),
     (safe_tac (ZF_cs addSEs [LFreeInE] addSEs LTermOcc.Tag.free_SEs)),
     (dtac (prem RS LOcc_in_Occ_range RS Occ_range_CorrectArityD) 1),
     (asm_full_simp_tac (ZF_ss addsimps LTermOcc.Arity_eqns) 1)]);

qed_goal "LFO_LLam_not_Nil" LLambda.thy
    "y: LVariable ==> domain(LFO(x, LLam(y, M))) ~= {[]}"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (excluded_middle_tac "x = y" 1),
     (hyp_subst_tac 2),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps LFO_eqns))),
     (ALLGOALS (rtac notI)),
     (ALLGOALS (dtac (equalityD2 RS singleton_subsetD))),
     (ALLGOALS (fast_tac (ZF_cs addSEs list.free_SEs
                        addSEs [Occ_shiftE])))]);

qed_goal "LFO_LApp_not_Nil" LLambda.thy
    "[| M: LTerm; N: LTerm |] ==> domain(LFO(x, LApp(M, N))) ~= {[]}"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_simp_tac (IFOL_ss addsimps LFO_eqns) 1),
     (rtac notI 1),
     (dtac (equalityD2 RS singleton_subsetD) 1),
     (fast_tac (ZF_cs addSEs list.free_SEs addSEs [Occ_shiftE]) 1)]);

qed_goalw "Lsubst_type" LLambda.thy [Lsubst_def]
    "[| M: LTerm; N: LTerm |] ==> Lsubst(M, x, N): LTerm"
  (fn [prem1, prem2] =>
    [(rtac (LTermOcc.use_thm def_graft_type) 1),
     (REPEAT (ares_tac [prem1, prem2, Incomparable_LFO, domain_mono,
                      LFO_subset_LOcc] 1))]);

qed_goalw "Lsubst_LVar1" LLambda.thy [Lsubst_def]
    "[| x: LVariable; N: LTerm |] ==> Lsubst(LVar(x), x, N) = N"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_simp_tac (IFOL_ss addsimps LFO_eqns) 1),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps 
          [domain_cons, domain_0, LTermOcc.use_thm def_graft_Nil]) 1)]);

qed_goalw "Lsubst_LVar2" LLambda.thy [Lsubst_def]
    "[| x ~= y; y: LVariable |] ==> Lsubst(LVar(y), x, N) = LVar(y)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_simp_tac (IFOL_ss addsimps LFO_eqns) 1),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps 
                  [domain_0, LTermOcc.use_thm def_graft_0]) 1)]);

qed_goalw "Lsubst_LLam1" LLambda.thy [Lsubst_def]
    "[| x: LVariable; M: LTerm |] ==> Lsubst(LLam(x, M), x, N) = LLam(x, M)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_simp_tac (IFOL_ss addsimps LFO_eqns) 1),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps 
                  [domain_0, LTermOcc.use_thm def_graft_0]) 1)]);

qed_goalw "Lsubst_LLam2" LLambda.thy [Lsubst_def]
    "[| x ~= y; y: LVariable; M: LTerm; N: LTerm |] ==> \
\        Lsubst(LLam(y, M), x, N) = LLam(y, Lsubst(M, x, N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (subgoals_tac ["domain(LFO(x, LLam(y, M))) ~= {[]}",
                  "Incomparable(domain(LFO(x, LLam(y, M))))",
                  "domain(LFO(x, LLam(y, M))) <= domain(LOcc(LLam(y, M)))",
                  "LFO(x, M) <= list(nat) * LTag"] 1),
     (asm_full_simp_tac (IFOL_ss addsimps LFO_eqns) 1),
     (asm_full_simp_tac (LTermOcc.Term_cons_ss addsimps 
                  [lists_subtree_domain_eq, LTermOcc.use_thm def_graft]
                       addsimps Occ_subtree_simps) 1),
     (rtac (LFO_subset_LOcc RS subset_trans) 1),
     (REPEAT (ares_tac ([LOcc_domain, LFO_subset_LOcc, domain_mono, 
                       Incomparable_LFO, LFO_LLam_not_Nil]
                      @ LTerm.intrs) 1))]);

qed_goalw "Lsubst_LApp" LLambda.thy [Lsubst_def]
    "[| A: LTerm; B: LTerm; N: LTerm |] ==> \
\        Lsubst(LApp(A, B), x, N) = LApp(Lsubst(A, x, N), Lsubst(B, x, N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (subgoals_tac ["domain(LFO(x, LApp(A, B))) ~= {[]}",
                  "Incomparable(domain(LFO(x, LApp(A, B))))",
                  "domain(LFO(x, LApp(A, B))) <= domain(LOcc(LApp(A, B)))",
                  "LFO(x, A) <= list(nat) * LTag",
                  "LFO(x, B) <= list(nat) * LTag"] 1),
     (asm_full_simp_tac (IFOL_ss addsimps LFO_eqns) 1),
     (asm_full_simp_tac (LTermOcc.Term_cons_ss addsimps 
                  [lists_subtree_domain_eq, LTermOcc.use_thm def_graft]
                       addsimps Occ_subtree_simps) 1),
     (REPEAT (ares_tac ([[LFO_subset_LOcc, LOcc_domain] MRS subset_trans, 
                       LFO_subset_LOcc, domain_mono, 
                       Incomparable_LFO, LFO_LApp_not_Nil]
                      @ LTerm.intrs) 1))]);

qed_goalw "Lsubst_0" LLambda.thy [Lsubst_def]
    "[| M: LTerm; x ~: LFV(M) |] ==> Lsubst(M, x, N) = M"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (res_inst_tac [("P", "%x. Lgraft(?X, x, ?Y) = ?Z")] subst 1),
     (etac (LTermOcc.use_thm def_graft_0) 2),
     (rtac equalityI 1),
     (fast_tac ZF_cs 1),
     (rtac subsetI 1),
     (etac notE 1),
     (fast_tac (ZF_cs addSEs [LFO_E] addIs [LFV_I]) 1)]);

val Lsubst_eqns = [Lsubst_LVar1, Lsubst_LVar2, Lsubst_LLam1, Lsubst_LLam2,
                   Lsubst_LApp, Lsubst_0];

val LTerm_ss = nth_ss addsimps (Lsubst_eqns @ LFV_eqns @ LFO_eqns)
    addsimps LTermOcc.Arity_eqns
    setsolver (type_auto_tac ([Lsubst_type] @ LTerm.intrs @
                              LTerm_Term_cons_typechecks));

qed_goal "Lsubst_self" LLambda.thy
    "[| x: LVariable; M: LTerm |] ==> Lsubst(M, x, LVar(x)) = M"
  (fn [prem1, prem2] =>
    [(cut_facts_tac [prem1 RS (hd LTerm.intrs)] 1),
     (LTermOcc.ind_tac "M" [prem2] 1),
     (excluded_middle_tac "x = xa" 2),
     (excluded_middle_tac "x = xa" 1),
     (TRYALL hyp_subst_tac),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps Lsubst_eqns)))]);


(** LFreeForIn **)
qed_goalw "LFreeForInE" LLambda.thy [LFreeForIn_def]
    "[| LFreeForIn(N, x, M); \
\       [| M: LTerm; N: LTerm; x: LVariable; \
\          ALL z l m. z: LFV(N) & LFreeIn(<l, TLVar(x)>, M) & \
\          <m, TLLam(z)>: LOcc(M) & initseg(nat, m, l) --> False \
\       |] ==> R\
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (fast_tac (ZF_cs addIs [prem]) 1)]);

qed_goalw "LFreeForInD1" LLambda.thy [LFreeForIn_def]
    "LFreeForIn(N, x, M) ==> N: LTerm"
  (fn [major] =>
    [(rtac (major RS conjunct1) 1)]);

qed_goalw "LFreeForInD2" LLambda.thy [LFreeForIn_def]
    "LFreeForIn(N, x, M) ==> x: LVariable"
  (fn [major] =>
    [(rtac (major RS conjunct2 RS conjunct1) 1)]);

qed_goalw "LFreeForInD3" LLambda.thy [LFreeForIn_def]
    "LFreeForIn(N, x, M) ==> M: LTerm"
  (fn [major] =>
    [(rtac (major RS conjunct2 RS conjunct2 RS conjunct1) 1)]);

qed_goalw "LFreeForInI" LLambda.thy [LFreeForIn_def]
    "[| N: LTerm; x: LVariable; M: LTerm;\
\       !! z l m. [| z: LFV(N); LFreeIn(<l, TLVar(x)>, M); \
\         <m, TLLam(z)>: LOcc(M); initseg(nat, m, l) |] ==> False \
\    |] ==> LFreeForIn(N, x, M)"
  (fn prems =>
    [(fast_tac (ZF_cs addIs prems) 1)]);

qed_goal "LFreeForIn_LVarI" LLambda.thy
    "[| x: LVariable; y: LVariable; N: LTerm |] \
\           ==>  LFreeForIn(N, x, LVar(y))"
  (fn prems =>
    [(rtac LFreeForInI 1),
     (eresolve_tac LOcc_LTermEs 4),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs) 4),
     (REPEAT (ares_tac (prems @ LTerm.intrs) 1))]);

qed_goal "LFreeForIn_LLamI1" LLambda.thy
    "[| N: LTerm; x: LVariable; M: LTerm |] ==> \
\         LFreeForIn(N, x, LLam(x, M))"
  (fn prems =>
    [(rtac LFreeForInI 1),
     (eresolve_tac LFreeIn_LTermEs 4),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs) 4),
     (REPEAT (ares_tac (prems @ LTerm.intrs) 1))]);

qed_goal "LFreeForIn_LLamI2" LLambda.thy
    "[| y: LVariable; LFreeForIn(N, x, M); \
\         [| y: LFV(N); x: LFV(M); y ~= x |] ==> False \
\     |] ==> LFreeForIn(N, x, LLam(y, M))"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem2 RS LFreeForInE) 1),
     (rtac LFreeForInI 1),
     (safe_tac (ZF_cs addSEs LFreeIn_LTermEs addSEs [initseg_left_ConsE]
              addSEs LTermOcc.Tag.free_SEs addSEs LOcc_LTermEs
              addSEs list.free_SEs)),
     (rtac prem3 2),
     (etac (spec RS spec RS spec RS mp) 5),
     (REPEAT (ares_tac (LTerm.intrs @ [LFV_I, conjI, prem1]) 1))]);

qed_goal "LFreeForIn_LLamI3" LLambda.thy
    "[| x ~: LFV(M); M: LTerm; N: LTerm; x: LVariable; y: LVariable |] ==>\
\           LFreeForIn(N, x, LLam(y, M))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac LFreeForInI 1),
     (REPEAT (ares_tac LTerm.intrs 1)),
     (safe_tac (ZF_cs addSEs LOcc_LTermEs addSEs LFreeIn_LTermEs
              addSEs LTermOcc.Tag.free_SEs addSEs [initseg_left_ConsE]
              addSEs list.free_SEs)),
     (REPEAT ((etac notE 1) THEN (etac LFV_I 1)))]);

qed_goal "LFreeForIn_LAppI" LLambda.thy
    "[| LFreeForIn(N, x, A); LFreeForIn(N, x, B) |] \
\            ==> LFreeForIn(N, x, LApp(A, B))"
  (fn [prem1, prem2] =>
    [(rtac (prem1 RS LFreeForInE) 1),
     (rtac (prem2 RS LFreeForInE) 1),
     (rtac LFreeForInI 1),
     (REPEAT (ares_tac LTerm.intrs 1)),
     (safe_tac (ZF_cs addSEs LFreeIn_LTermEs addSEs [initseg_left_ConsE]
              addSEs LTermOcc.Tag.free_SEs addSEs LOcc_LTermEs
              addSEs list.free_SEs)),
     (REPEAT (((etac (spec RS spec RS spec RS mp) 1) THEN
             (rtac conjI 1) THEN 
             (atac 1) THEN 
             (rtac conjI 1) THEN 
             (atac 1)) ORELSE (ares_tac [conjI] 1)))]);

val LFreeForIn_LTermIs = [LFreeForIn_LVarI, LFreeForIn_LLamI1,
                          LFreeForIn_LLamI2, LFreeForIn_LAppI];

qed_goal "LFreeForIn_LVarE" LLambda.thy
    "[| LFreeForIn(N, x, LVar(y)); \
\       [| x: LVariable; y: LVariable; N: LTerm |] ==> R |] ==> R"
  (fn [major, prem1] =>
    [(rtac (major RS LFreeForInE) 1),
     (eresolve_tac LTerm_typeEs 1),
     (REPEAT (ares_tac [prem1] 1))]);

qed_goal "LFreeForIn_LLamE" LLambda.thy
    "[| LFreeForIn(N, x, LLam(y, M)); \
\       [| x = y; x: LVariable; N: LTerm; M: LTerm |] ==> R; \
\       [| x ~= y; y: LVariable; LFreeForIn(N, x, M); \
\          x: LFV(M); y ~: LFV(N) |] ==> R; \
\       [| x ~= y; y: LVariable; N: LTerm; x: LVariable; x ~: LFV(M)|] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (major RS LFreeForInE) 1),
     (eresolve_tac LTerm_typeEs 1),
     (excluded_middle_tac "x = y" 1),
     (rtac prem1 2),
     (REPEAT (atac 2)),
     (excluded_middle_tac "x: LFV(M)" 1),
     (rtac prem3 1),
     (REPEAT (atac 1)),
     (etac LFV_E 1),
     (rtac prem2 1),
     (rtac LFreeForInI 3),
     (etac (spec RS spec RS spec RS mp) 6),
     (rtac conjI 6),
     (rtac conjI 7),
     (rtac conjI 8),
     (rtac initseg_ConsI 9),
     (atac 10),
     (resolve_tac LFreeIn_LTermIs 7),
     (fast_tac ZF_cs 8),
     (REPEAT (ares_tac ([conjI, nat_0I, initseg_ConsI, LFV_I] 
                        @ LOcc_LTermIs) 1)),
     (rtac notI 1),
     (etac (spec RS spec RS spec RS mp) 1),
     (REPEAT (ares_tac ([conjI, nat_0I, initseg_NilI] @ LOcc_LTermIs
                        @ LFreeIn_LTermIs
                        @ list.intrs) 1)),
     (etac LFreeInE2 1),
     (rtac (LOcc_domain RS subsetD RS SigmaD1) 1),
     (atac 2),
     (atac 1)]);

qed_goal "LFreeForIn_LAppE" LLambda.thy
    "[| LFreeForIn(N, x, LApp(A, B)); \
\       [| LFreeForIn(N, x, A); LFreeForIn(N, x, B) |] ==> R |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS LFreeForInE) 1),
     (eresolve_tac LTerm_typeEs 1),
     (rtac prem 1),
     (ALLGOALS (etac LFreeForInI)),
     (TRYALL atac),
     (ALLGOALS (etac (spec RS spec RS spec RS mp))),
     (REPEAT ((eresolve_tac (LFreeIn_LTermIs @ LOcc_LTermIs) 1) ORELSE
            (ares_tac [conjI, initseg_ConsI, nat_0I, nat_1I] 1)))]);

val LFreeForIn_LTermEs = [LFreeForIn_LVarE, LFreeForIn_LLamE,
                          LFreeForIn_LAppE];

qed_goal "LFreeForIn_left_LVarI" LLambda.thy
    "[| x: LVariable; M: LTerm |] ==> LFreeForIn(LVar(x), x, M)"
  (fn prems =>
    [(rtac LFreeForInI 1),
     (etac LFreeInE2 4),
     (safe_tac (ZF_cs addSEs LFreeIn_LTermEs
              addSEs [LFV_E] addSEs LTermOcc.Tag.free_SEs)),
     (etac (spec RS mp RS notE) 4),
     (REPEAT (ares_tac (prems @ LTerm.intrs) 1))]);

qed_goal "TLVar_free_or_bound" LLambda.thy
    "[| <l, TLVar(x)>: LOcc(M); M: LTerm |] \
\        ==> LFreeIn(<l, TLVar(x)>, M) | LBoundIn(<l, TLVar(x)>, M)"
  (fn [prem1, prem2] =>
    [(excluded_middle_tac "LBoundIn(<l, TLVar(x)>, M)" 1),
     (rtac disjI1 1),
     (rtac LFreeInI2 1),
     (etac notE 3),
     (rtac LBoundInI 3),
     (REPEAT (ares_tac [prem1, prem2, exI, disjI2] 1))]);

qed_goal "DenseTree_CorrectArity_0D" OccTools.thy
    "[| DenseTree(X); CorrectArity(X, T, 0); \
\       <l, T>: X; <m, U>: X; initseg(nat, l, m) \
\    |] ==> l = m"
  (fn [hier, corrT, prem1, prem2, prem3] =>
    [(rtac (prem3 RS initsegE) 1),
     (eres_inst_tac [("a", "x")] list.elim 1),
     (ALLGOALS bound_hyp_subst_tac),
     (asm_simp_tac (IFOL_ss addsimps [app_right_Nil]) 1),
     (rtac (hier RS DenseTreeE) 1),
     (rtac prem2 1),
     (hyp_subst_tac 1),
     (REPEAT (ares_tac [initseg_appI2, initseg_ConsI, initseg_NilI] 1)),
     (rtac (corrT RS CorrectArityD2 RS notE) 1),
     (REPEAT (ares_tac [prem1, exI, nat_into_Ord RS Ord_0_le] 1))]);

qed_goal "TLVar_leaf" LLambda.thy
    "[| <l, TLVar(x)>: LOcc(M); <m, T>: LOcc(M); initseg(nat, l, m); \
\        M: LTerm |] ==> m = l & T = TLVar(x)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (forward_tac [LOcc_in_Occ_range] 1),
     (etac Occ_rangeE 1),
     (subgoals_tac ["m = l"] 1),
     (etac (DenseTree_CorrectArity_0D RS sym) 2),
     (REPEAT (atac 3)),
     (dres_inst_tac [("x", "TLVar(x)")] bspec 2),
     (asm_full_simp_tac LTerm_ss 3),
     (etac LOcc_typeD2 2),
     (safe_tac ZF_cs),
     (etac functionalD 1),
     (REPEAT (atac 1))]);

qed_goalw "LOcc_LsubstE" LLambda.thy [Lgraft_def, Lsubst_def]
    "[| u: LOcc(Lsubst(M, x, N)); M: LTerm; N: LTerm; \
\       !! l T. [| u = <l, T>; <l, T>: LOcc(M); <l, T> ~: LFO(x, M) |] \
\              ==> R; \
\       !!m l T. [| u = <m @ l, T>; <m, TLVar(x)>: LFO(x, M); \
\           <l, T>: LOcc(N) |] ==> R \
\    |] ==> R"
  (fn [major, M_term, N_term, prem1, prem2] =>
    [(cut_facts_tac [M_term, N_term] 1),
     (subgoals_tac ["Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N)): \
\       Occ_range(LTag, LArity)"] 1),
     (REPEAT (ares_tac [LTermOcc.use_thm Occ_Graft_in_Occ_range2,
                      LOcc_in_Occ_range, Incomparable_LFO,
                      LFO_subset_LOcc RS domain_mono] 2)),
     (cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps 
                       [LTermOcc.use_thm def_Occ_Occinv]) 1),
     (etac Occ_GraftE 1),
     (etac LOcc_domain 1),
     (etac Occ_ShiftE 2),
     (etac domainE 2),
     (rtac prem2 2),
     (rtac prem1 1),
     (safe_tac (ZF_cs addSEs [LFO_E] addSEs LTermOcc.Tag.free_SEs)),
     (etac LFO_I 5),
     (TRYALL (ares_tac [refl])),
     (etac notE 1),
     (rtac bexI 1),
     (etac (LFO_I RS domainI) 2),
     (REPEAT (ares_tac [initseg_refl] 1))]);

qed_goalw "LOcc_LsubstI1" LLambda.thy [Lgraft_def, Lsubst_def]
    "[| <l, T> ~: LFO(x, M); <l, T>: LOcc(M); M: LTerm; N: LTerm |] \
\      ==> <l, T>: LOcc(Lsubst(M, x, N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (subgoals_tac ["Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N)): \
 \       Occ_range(LTag, LArity)"] 1),
     (REPEAT (ares_tac [LTermOcc.use_thm Occ_Graft_in_Occ_range2,
                      LOcc_in_Occ_range, Incomparable_LFO,
                      LFO_subset_LOcc RS domain_mono] 2)),
     (asm_full_simp_tac (IFOL_ss addsimps 
                       [LTermOcc.use_thm def_Occ_Occinv]) 1),
     (rtac Occ_GraftI1 1),
     (atac 1),
     (safe_tac (ZF_cs addSEs [LFO_E, LFreeInE2])),
     (subgoals_tac ["TLVar(x): LTag", "la = l", "T = TLVar(x)"] 1),
     (rtac (LOcc_domain RS subsetD RS SigmaD2) 4),
     (atac 5),
     (rtac (LOcc_in_Occ_range RS Occ_rangeE) 3),
     (atac 3),
     (etac DenseTree_CorrectArity_0D 3),
     (REPEAT (atac 4)),
     (dres_inst_tac [("x", "TLVar(x)")] bspec 3),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Arity_eqns) 4),
     (hyp_subst_tac 2),
     (etac (LOcc_in_Occ_range RS Occ_range_functionalD RS functionalD) 2),
     (REPEAT (atac 2)),
     (hyp_subst_tac 1),
     (etac notE 1),
     (rtac (LFreeInI RS LFO_I) 1),
     (etac (spec RS mp RS notE) 3),
     (REPEAT (atac 1))]);

qed_goalw "LOcc_LsubstI2" LLambda.thy [Lgraft_def, Lsubst_def]
    "[| <m, TLVar(x)>: LFO(x, M); <l, T>: LOcc(N); M: LTerm; N: LTerm |] \
\       ==> <m @ l, T>: LOcc(Lsubst(M, x, N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (subgoals_tac ["Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N)): \
 \       Occ_range(LTag, LArity)"] 1),
     (REPEAT (ares_tac [LTermOcc.use_thm Occ_Graft_in_Occ_range2,
                      LOcc_in_Occ_range, Incomparable_LFO,
                      LFO_subset_LOcc RS domain_mono] 2)),
     (asm_full_simp_tac (IFOL_ss addsimps 
                       [LTermOcc.use_thm def_Occ_Occinv]) 1),
     (rtac Occ_GraftI2 1),
     (etac domainI 1),
     (etac Occ_ShiftI 1)]);

qed_goalw "LBoundBy_LsubstE" LLambda.thy [Lgraft_def, Lsubst_def]
    "[| LBoundBy(<l, TLVar(y)>, <m, TLLam(y)>, Lsubst(M, x, N)); \
\       LFreeForIn(N, x, M); \
\       LBoundBy(<l, TLVar(y)>, <m, TLLam(y)>, M) ==> R; \
\       !!n a b. [| l =  n @ a; m = n @ b; <n, TLVar(x)>: LFO(x, M); \
\         LBoundBy(<a, TLVar(y)>, <b, TLLam(y)>, N) |] ==> R \
\    |] ==> R"
  (fn [major, sub, prem1, prem2] =>
    [(rtac (sub RS LFreeForInE) 1),
     (subgoals_tac ["Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N)): \
\       Occ_range(LTag, LArity)"] 1),
     (cut_facts_tac [major] 1),
     (REPEAT (ares_tac [LTermOcc.use_thm Occ_Graft_in_Occ_range2,
                      LOcc_in_Occ_range, Incomparable_LFO,
                      LFO_subset_LOcc RS domain_mono] 2)),
     (etac LBoundByE 1),
     (etac LBindingE2 1),
     (asm_full_simp_tac (IFOL_ss addsimps [LTermOcc.use_thm def_Occ_Occinv]) 1),
     (REPEAT (CHANGED (TRYALL (eresolve_tac 
                             [Occ_ShiftE2, LOcc_domain RSN (2, Occ_GraftE)])))),
     (TRYALL atac),
     (ALLGOALS (REPEAT o (bound_hyp_subst_tac))),
     (etac initseg_left_appE 4),
     (etac domainE 4),
     (etac ([LFO_subset_LOcc, LOcc_domain] MRS subset_trans RS subsetD RS
          SigmaD1) 4),
     (atac 4),
     (rtac prem2 4),
     (rtac prem1 1),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs addSEs [LFO_E]
              addSIs [LFO_I])),
     (REPEAT (ares_tac [refl] 4)),
    (**)
     (etac notE 3),
     (subgoals_tac ["lc: list(nat)"] 3),
     (etac LFreeInE2 4),
     (etac (LOcc_domain RS subsetD RS SigmaD1) 4),
     (atac 4),
     (rtac bexI 3),
     (etac (LFO_I RS domainI) 4),
     (etac initseg_left_appE 3),
     (atac 3),
     (hyp_subst_tac 3),
     (rtac initseg_appI1 3),
     (etac app_typeD 4),
     (REPEAT (atac 3)),
    (* 31 *)
     (subgoals_tac ["lc: list(nat)"] 2),
     (etac LFreeInE2 3),
     (etac (LOcc_domain RS subsetD RS SigmaD1) 3),
     (atac 3),
     (etac initseg_right_appE 2),
     (etac notE 4),
     (rtac bexI 4),
     (atac 4),
     (etac (LFO_I RS domainI) 4),
     (atac 2),
     (etac (TLVar_free_or_bound RS disjE) 2),
     (atac 2),
     (etac (spec RS spec RS spec RS notE) 2),
     (REPEAT (ares_tac [conjI, LFV_I] 2)),
     (etac LBoundInE 2),
     (dtac LBinding_imp_LBoundBy_lemma 2),
     (etac exE 2),
     (etac LBoundByE 2),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs addSEs [LBindingE2])),
     (dtac (spec RS mp RS mp) 2),
     (rtac LBindingI 3),
     (rtac initseg_appI2 6),
     (atac 7),
     (rtac initseg_trans 2),
     (atac 2),
     (rtac initseg_appI1 2),
     (etac initsegD1 3),
    (**)
     (asm_full_simp_tac (IFOL_ss addsimps [LTermOcc.use_thm def_Occ_Occinv]) 4),
     (asm_full_simp_tac (IFOL_ss addsimps [LTermOcc.use_thm def_Occ_Occinv]) 5),
     (rtac Occ_GraftI2 4),
     (etac (LFO_I RS domainI) 4),
     (etac Occ_ShiftI 4),
     (rtac Occ_GraftI2 4),
     (etac (LFO_I RS domainI) 4),
     (etac Occ_ShiftI 4),
     (hyp_subst_tac 5),
     (etac initseg_left_appE 5),
     (dtac (sym RS app_Nil_eqD1) 6),
     (hyp_subst_tac 7),
     (etac initseg_NilE 7),
     (hyp_subst_tac 7),
     (subgoals_tac [("TLLam(y) = TLVar(x)")] 7),
     (etac (LOcc_in_Occ_range RS Occ_range_functionalD RS functionalD) 8),
     (atac 8),
     (etac LFreeInE 8),
     (asm_full_simp_tac (IFOL_ss addsimps [app_right_Nil]
                       addsimps LTag_simps) 8),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs) 7),
     (REPEAT (atac 2)),
    (**)
     (ALLGOALS (rtac LBoundByI)),
     (TRYALL (rtac LBindingI)),
     (TRYALL atac),
     (SELECT_GOAL
    (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs addSEs [LFreeInE])) 2),
     (etac app_appE 2),
     (REPEAT (ares_tac [LOcc_domain RS subsetD RS SigmaD1] 2)),
     (hyp_subst_tac 2),
     (eres_inst_tac [("a", "z")] list.elim 2),
     (hyp_subst_tac 2),
     (asm_full_simp_tac list_ss 2),
     (eres_inst_tac [("a", "z")] list.elim 3),
     (hyp_subst_tac 3),
     (asm_full_simp_tac list_ss 3),
    (* 92 *)
     (hyp_subst_tac 2),
     (etac (LOcc_in_Occ_range RS Occ_rangeE) 2),
     (eres_inst_tac [("l", "lg @ Cons(a, lh)")] DenseTreeE 2),
     (rtac initseg_appI2 3),
     (rtac initseg_ConsI 4),
     (rtac initseg_NilI 5),
     (rtac (LOcc_domain RS subsetD RS SigmaD1) 3),
     (atac 4),
     (REPEAT (atac 2)),
     (etac (bspec RS CorrectArityD2 RS notE) 2),
     (etac exI 5),
     (atac 3),
     (asm_simp_tac (ZF_ss addsimps LTermOcc.Arity_eqns) 3),
     (eresolve_tac LTermOcc.Tag.intrs 2),
     (etac (nat_into_Ord RS Ord_0_le) 2),
    (**)
     (hyp_subst_tac 2),
     (etac (LOcc_in_Occ_range RS Occ_rangeE) 2),
     (eres_inst_tac [("l", "lf @ Cons(a, lh)")] DenseTreeE 2),
     (rtac initseg_appI2 3),
     (rtac initseg_ConsI 4),
     (rtac initseg_NilI 5),
     (rtac (LOcc_domain RS subsetD RS SigmaD1) 3),
     (atac 4),
     (REPEAT (atac 2)),
     (etac (bspec RS CorrectArityD2 RS notE) 2),
     (etac exI 5),
     (atac 3),
     (asm_simp_tac (ZF_ss addsimps LTermOcc.Arity_eqns) 3),
     (eresolve_tac LTermOcc.Tag.intrs 2),
     (etac (nat_into_Ord RS Ord_0_le) 2),
    (* 122 *)
     (subgoals_tac [("ld: list(nat)")] 2),
     (REPEAT (etac LFreeInE2 3)),
     (rtac (LOcc_domain RS subsetD RS SigmaD1) 3),
     (atac 4),
     (atac 3),
     (rtac (app_right_inj_iff RS iffD1) 2),
     (etac (spec RS mp RS mp) 3),
     (rtac initseg_appI2 3),
     (REPEAT (atac 2)),
     (rtac LBindingI 2),
     (etac ssubst 5),
     (rtac initseg_appI2 5),
     (etac LBindingE2 6),
     (REPEAT (atac 5)),
     (etac (spec RS mp RS mp) 1),
     (rtac LBindingI 2),
     (etac LBindingE2 5),
     (TRYALL atac),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps 
                            [LTermOcc.use_thm def_Occ_Occinv]))),
     (ALLGOALS (etac LBindingE2)),
    (**)
     (rtac Occ_GraftI2 3),
     (etac Occ_ShiftI 4),
     (etac (LFO_I RS domainI) 3),
     (rtac Occ_GraftI2 3),
     (etac Occ_ShiftI 4),
     (etac (LFO_I RS domainI) 3),
    (**)
     (ALLGOALS (rtac Occ_GraftI1)),
     (TRYALL atac),
     (rtac notI 1),
     (etac bexE 1),
     (etac notE 1),
     (etac notE 1),
     (rtac bexI 1),
     (atac 2),
     (etac initseg_trans 1),
     (atac 1)]);

qed_goalw "LBoundBy_LsubstI1" LLambda.thy [Lgraft_def, Lsubst_def]
    "[| LBoundBy(<l, TLVar(y)>, <m, TLLam(y)>, M); N: LTerm |]  \
\      ==> LBoundBy(<l, TLVar(y)>, <m, TLLam(y)>, Lsubst(M, x, N))"
  (fn [major, prem] =>
    [(rtac (major RS LBoundByE2) 1),
     (etac LBindingE2 1),
     (subgoals_tac ["Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N)): \
\       Occ_range(LTag, LArity)"] 1),
     (REPEAT (ares_tac [LTermOcc.use_thm Occ_Graft_in_Occ_range2,
                      LOcc_in_Occ_range, Incomparable_LFO,
                      LFO_subset_LOcc RS domain_mono, prem] 2)),
     (rtac LBoundByI 1),
     (etac LBindingE2 2),
     (rtac LBindingI 1),
     (ALLGOALS (asm_full_simp_tac 
              (IFOL_ss addsimps [LTermOcc.use_thm def_Occ_Occinv]))),
     (etac (LTermOcc.use_thm def_Occinv_type) 1),
     (rtac Occ_GraftI1 2),
     (rtac Occ_GraftI1 1),
     (TRYALL atac),
     (TRYALL (rtac notI)),
     (safe_tac (ZF_cs addSEs [LFO_E, LFreeInE2])),
    (**)
     (rtac (LOcc_in_Occ_range RS Occ_rangeE) 1),
     (atac 1),
     (dres_inst_tac [("T", "TLVar(x)")] DenseTree_CorrectArity_0D 1),
     (atac 2),
     (atac 3),
     (atac 2),
     (dres_inst_tac [("x", "TLVar(x)")] bspec 1),
     (etac (LOcc_domain RS subsetD RS SigmaD2) 1),
     (atac 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Arity_eqns) 1),
     (hyp_subst_tac 1),
     (subgoals_tac ["TLLam(y) = TLVar(x)"] 1),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs) 1),
     (etac functionalD 1),
     (REPEAT (atac 1)),
    (**)
     (rtac (LOcc_in_Occ_range RS Occ_rangeE) 1),
     (atac 1),
     (dres_inst_tac [("T", "TLVar(x)")] DenseTree_CorrectArity_0D 1),
     (atac 2),
     (atac 3),
     (atac 2),
     (dres_inst_tac [("x", "TLVar(x)")] bspec 1),
     (etac (LOcc_domain RS subsetD RS SigmaD2) 1),
     (atac 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Arity_eqns) 1),
     (hyp_subst_tac 1),
     (subgoals_tac ["TLVar(y) = TLVar(x)"] 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTag_simps) 1),
     (hyp_subst_tac 1),
     (etac (spec RS mp RS notE) 1),
     (etac functionalD 3),
     (REPEAT (atac 1)),
    (**)
     (etac (spec RS mp RS mp) 1),
     (atac 1),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs 
              addSEs [LOcc_domain RSN (2, Occ_GraftE), Occ_ShiftE])),
     (subgoals_tac ["ma: list(nat)"] 3),
     (etac ([LFO_subset_LOcc, LOcc_domain] MRS subset_trans RS subsetD
          RS SigmaD1) 4),
     (atac 4),
     (subgoals_tac ["ma: list(nat)"] 4),
     (etac ([LFO_subset_LOcc, LOcc_domain] MRS subset_trans RS subsetD
          RS SigmaD1) 5),
     (atac 5),
    (**)
     (etac initseg_left_appE 3),
     (hyp_subst_tac 4),
     (etac notE 4),
     (rtac bexI 4),
     (etac domainI 5),
     (rtac initseg_appI1 4),
     (etac initsegD2 5),
    (**)
     (etac initseg_left_appE 5),
     (asm_simp_tac IFOL_ss 6),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs [LFO_E, LFreeInE2])) 6),
     (subgoals_tac ["ld: list(nat)"] 6),
     (etac (LOcc_domain RS subsetD RS SigmaD1) 7),
     (atac 7),
     (rtac (LOcc_in_Occ_range RS Occ_rangeE) 6),
     (atac 6),
     (dres_inst_tac [("l", "lc")] DenseTree_CorrectArity_0D 6),
     (atac 7),
     (etac (sym RS initsegI) 8),
     (etac initsegD2 8),
     (atac 7),
     (REPEAT (ares_tac [LBindingI] 1)),
     (dres_inst_tac [("x", "TLVar(x)")] bspec 1),
     (etac (LOcc_domain RS subsetD RS SigmaD2) 1),
     (atac 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Arity_eqns) 1),
     (REPEAT (ares_tac [app_type] 1)),
     (etac (prem RS LOcc_domain RS subsetD RS SigmaD1) 1),
     (hyp_subst_tac 1),
     (subgoals_tac ["TLVar(y) = TLVar(x)"] 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTag_simps) 1),
     (hyp_subst_tac 1),
     (etac (spec RS mp RS notE) 1),
     (atac 2),
     (etac functionalD 2),
     (REPEAT (atac 1))]);

qed_goalw "LBoundBy_LsubstI2" LLambda.thy [Lgraft_def, Lsubst_def]
    "[| LBoundBy(<l, TLVar(y)>, <m, TLLam(y)>, N); \
\      <n, TLVar(x)>: LFO(x, M) \
\    |] ==> LBoundBy(<n@l, TLVar(y)>, <n@m, TLLam(y)>, Lsubst(M, x, N))"
  (fn [major, prem] =>
    [(rtac (major RS LBoundByE2) 1),
     (etac LBindingE2 1),
     (subgoals_tac ["n: list(nat)", "M: LTerm",
                  "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N)): \
                   \       Occ_range(LTag, LArity)"] 1),
     (REPEAT (ares_tac [LTermOcc.use_thm Occ_Graft_in_Occ_range2,
                      LOcc_in_Occ_range, Incomparable_LFO,
                      LFO_subset_LOcc RS domain_mono, prem] 2)),
     (rtac (prem RS LFO_E2) 2),
     (etac LFreeInE2 2),
     (atac 2),
     (rtac (prem RS LFO_E2) 2),
     (etac LFreeInE2 2),
     (rtac (LOcc_domain RS subsetD RS SigmaD1) 2),
     (atac 3),
     (atac 2),
    (**)
     (rtac LBoundByI 1),
     (etac LBindingE2 2),
     (rtac LBindingI 1),
     (ALLGOALS (asm_full_simp_tac 
              (IFOL_ss addsimps [LTermOcc.use_thm def_Occ_Occinv]))),
     (etac (LTermOcc.use_thm def_Occinv_type) 1),
     (etac initseg_left_appE 4),
     (atac 4),
     (bound_hyp_subst_tac 4),
     (REPEAT (etac (Occ_ShiftI RS (prem RS domainI RS Occ_GraftI2)) 1)),
     (rtac initseg_appI2 1),
     (REPEAT (atac 1)),
     (res_inst_tac [("f", "%x. n @ x")] function_apply_eq 1),
     (etac (spec RS mp RS mp) 1),
     (atac 1),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs 
              addSEs [LOcc_domain RSN (2, Occ_GraftE), Occ_ShiftE])),
     (etac initseg_left_appE 4),
     (subgoals_tac ["lc = l"] 5),
     (rtac (app_right_inj_iff RS iffD1 RS sym) 6),
     (atac 7),
     (hyp_subst_tac 5),
     (rtac LBindingI 5),
     (TRYALL atac),
    (**)
     (cut_facts_tac [prem] 4),
     (subgoals_tac ["ma: list(nat)",
                  "n = ma"] 4),
     (REPEAT (etac LFO_E 6)),
     (REPEAT (etac LFreeInE2 6)),
     (rtac (LOcc_domain RS subsetD RS SigmaD1) 6),
     (fast_tac ZF_cs 7),
     (atac 6),
     (eres_inst_tac [("x", "la")] app_appE 5),
     (subgoals_tac ["initseg(nat, ma, n)"] 8),
     (etac (sym RS initsegI) 9),
     (subgoals_tac ["initseg(nat, n, ma)"] 7),
     (etac (sym RS initsegI) 8),
     (TRYALL atac),
     (rtac (Incomparable_LFO RS IncomparableD RS sym) 6),
     (etac domainI 8),
     (rtac (Incomparable_LFO RS IncomparableD) 5),
     (etac domainI 7),
     (REPEAT (ares_tac [domainI] 5)),
     (hyp_subst_tac 4),
     (asm_full_simp_tac (IFOL_ss addsimps [app_right_inj_iff]) 4),
    (**)
     (REPEAT ((etac notE 1) THEN
            (rtac bexI 1) THEN
            (rtac (prem RS domainI) 2) THEN
            (etac initseg_appI1 1) THEN
            (etac initsegD2 1)))]);


qed_goal "LFreeIn_LsubstE" LLambda.thy
    "[| LFreeIn(<l, TLVar(y)>, Lsubst(M, x, N)); M: LTerm; N: LTerm; \
\       [| LFreeIn(<l, TLVar(y)>, M); x ~= y |] ==> R; \
\       !!n a b. [| l =  n @ a; LFreeIn(<n, TLVar(x)>, M); \
\          LFreeIn(<a, TLVar(y)>, N); \
\          ALL m. ~(initseg(nat, m, n) & <m, TLLam(y)>: LOcc(M))|] ==> R \
\    |] ==> R"
  (fn [major, M_term, N_term, prem1, prem2] =>
    [(cut_facts_tac [M_term, N_term] 1),
     (rtac (major RS LFreeInE2) 1),
     (etac LOcc_LsubstE 1),
     (rtac prem2 4),
     (safe_tac (ZF_cs addSEs [LFO_E2])),
     (rtac refl 2),
     (atac 2),
     (rtac LFreeInI2 2),
     (etac LBinding_imp_LBoundByE 4),
     (dtac LBoundBy_LsubstI2 4),
     (etac LFO_I 4),
     (etac (LBoundByD1 RS LBindingE2) 4),
     (rtac prem1 1),
     (rtac LFreeInI2 1),
     (etac LBinding_imp_LBoundByE 3),
     (dres_inst_tac [("N", "N"), ("x", "x")] LBoundBy_LsubstI1 3),
     (etac (LBoundByD1 RS LBindingE2) 4),
     (TRYALL atac),
     (rtac notI 2),
     (hyp_subst_tac 2),
     (etac notE 2),
     (rtac (LFreeInI RS LFO_I) 2),
     (etac (spec RS mp RS notE) 4),
     (rtac LOcc_LsubstI1 4),
     (atac 8),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs addSEs [LFO_E])),
     (ALLGOALS (etac (spec RS mp RS notE))),
     (TRYALL atac),
     (rtac LOcc_LsubstI1 1),
     (atac 2),
     (etac initseg_trans 4),
     (rtac initseg_appI1 4),
     (etac LOcc_typeD1 5),
     (etac LFreeInE2 4),
     (etac LOcc_typeD1 4),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs addSEs [LFO_E]))]);

qed_goal "LFreeIn_LsubstI1" LLambda.thy
    "[| LFreeIn(<l, TLVar(y)>, M); LFreeForIn(N, x, M); x ~= y |] \
\       ==> LFreeIn(<l, TLVar(y)>, Lsubst(M, x, N))"
  (fn [major, sub, prem] =>
    [(rtac (sub RS LFreeForInE) 1),
     (subgoals_tac ["Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N)): \
                   \       Occ_range(LTag, LArity)"] 1),
     (REPEAT (ares_tac [LTermOcc.use_thm Occ_Graft_in_Occ_range2,
                      LOcc_in_Occ_range, Incomparable_LFO,
                      LFO_subset_LOcc RS domain_mono] 2)),
     (rtac (major RS LFreeInE2) 1),
     (rtac LFreeInI2 1),
     (etac LBinding_imp_LBoundByE 3),
     (etac LBoundBy_LsubstE 3),
     (rtac sub 3),
     (rewrite_goals_tac [Lsubst_def]),
     (rtac (LTermOcc.use_thm def_graft_type) 1),
     (REPEAT (ares_tac [Incomparable_LFO, domain_mono, 
                      LFO_subset_LOcc] 1)),
     (rewrite_goals_tac [Lgraft_def]),
     (ALLGOALS (asm_full_simp_tac 
              (IFOL_ss addsimps [LTermOcc.use_thm def_Occ_Occinv]))),
     (rtac Occ_GraftI1 1),
     (atac 1),
     (rtac notI 1),
     (cut_facts_tac [prem] 1),
     (safe_tac (ZF_cs addSEs [LFO_E, LFreeInE]
              addSEs LTermOcc.Tag.free_SEs)),
     (etac (LOcc_in_Occ_range RS Occ_rangeE) 1),
     (dtac DenseTree_CorrectArity_0D 1),
     (atac 4),
     (REPEAT (atac 2)),
     (dres_inst_tac [("x", "TLVar(x)")] bspec 1),
     (eresolve_tac LTermOcc.Tag.intrs 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Arity_eqns) 1),
     (hyp_subst_tac 1),
     (subgoals_tac ["TLVar(x) = TLVar(y)"] 1),
     (etac functionalD 2),
     (REPEAT (atac 2)),
     (rtac (prem RS notE) 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTag_simps) 1),
     (ALLGOALS (etac (LBoundByD1 RS LBindingE2))),
     (etac (spec RS mp RS notE) 1),
     (REPEAT (atac 1)),
     (subgoals_tac ["lb: list(nat)"] 1),
     (etac (LOcc_in_Occ_range RS Occ_rangeE) 1),
     (dtac DenseTree_CorrectArity_0D 1),
     (rtac initseg_appI1 4),
     (atac 3),
     (atac 2),
     (etac initsegD2 3),
     (atac 2),
     (dres_inst_tac [("x", "TLVar(x)")] bspec 1),
     (eresolve_tac LTermOcc.Tag.intrs 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Arity_eqns) 1),
     (dtac (sym RS app_Nil_eqD1) 1),
     (atac 1),
     (hyp_subst_tac 1),
     (etac initseg_NilE 1),
     (hyp_subst_tac 1),
     (subgoals_tac ["TLLam(y) = TLVar(y)"] 1),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs) 1),
     (etac (LOcc_in_Occ_range RS Occ_range_functionalD RS functionalD) 1),
     (REPEAT (atac 1)),
     (rtac (LOcc_domain RS subsetD RS SigmaD1) 1),
     (atac 2),
     (atac 1)]);

qed_goal "LFreeIn_LsubstI2" LLambda.thy
    "[| LFreeIn(<l, TLVar(y)>, N); LFreeForIn(N, x, M); \
\       <n, TLVar(x)>: LFO(x, M) \
\    |] ==> LFreeIn(<n @ l, TLVar(y)>, Lsubst(M, x, N))"
  (fn [major, sub, prem] =>
    [(rtac (sub RS LFreeForInE) 1),
     (subgoals_tac ["n: list(nat)",
                  "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N)): \
                   \       Occ_range(LTag, LArity)"] 1),
     (REPEAT (ares_tac [LTermOcc.use_thm Occ_Graft_in_Occ_range2,
                      LOcc_in_Occ_range, Incomparable_LFO,
                      LFO_subset_LOcc RS domain_mono] 2)),
     (rtac (major RS LFreeInE2) 1),
     (rtac LFreeInI2 1),
     (etac LBinding_imp_LBoundByE 3),
     (etac LBoundBy_LsubstE 3),
     (rtac sub 3),
     (rewrite_goals_tac [Lsubst_def]),
     (rtac (LTermOcc.use_thm def_graft_type) 1),
     (REPEAT (ares_tac [Incomparable_LFO, domain_mono, 
                      LFO_subset_LOcc] 1)),
     (rewrite_goals_tac [Lgraft_def]),
     (ALLGOALS (asm_full_simp_tac 
              (IFOL_ss addsimps [LTermOcc.use_thm def_Occ_Occinv]))),
     (rtac Occ_GraftI2 1),
     (etac Occ_ShiftI 2),
     (rtac (prem RS domainI) 1),
     (rtac (prem RS LFO_E2) 1),
     (etac (LBoundByD1 RS LBindingE2) 1),
     (etac LFreeInE2 1),
    (**)
     (rtac (LOcc_in_Occ_range RS Occ_rangeE) 1),
     (dtac DenseTree_CorrectArity_0D 2),
     (rtac initseg_appI1 5),
     (atac 4),
     (atac 3),
     (dres_inst_tac [("x", "TLVar(x)")] bspec 2),
     (eresolve_tac LTermOcc.Tag.intrs 2),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Arity_eqns) 2),
     (rtac (LOcc_domain RS subsetD RS SigmaD1) 3),
     (atac 4),
     (REPEAT (atac 1)),
     (dtac (sym RS app_Nil_eqD1) 1),
     (atac 1),
     (hyp_subst_tac 1),
     (asm_full_simp_tac (IFOL_ss addsimps [app_right_Nil]) 1),
     (subgoals_tac ["TLVar(y) = TLVar(x)"] 1),
     (etac functionalD 2),
     (REPEAT (atac 2)),
     (eres_inst_tac [("P5", "%m. initseg(nat, m, n)")] 
      (spec RS mp RS notE) 1),
     (atac 2),
     (asm_full_simp_tac (IFOL_ss addsimps LTag_simps) 1),
     (hyp_subst_tac 1),
     (atac 1),
    (**)
     (etac (LBoundByD1 RS LBindingE2) 1),
     (cut_facts_tac [prem] 1),
     (subgoals_tac ["na: list(nat)", "na = n"] 1),
     (etac app_appE 2),
     (REPEAT (atac 2)),
     (rtac (Incomparable_LFO RS IncomparableD) 3),
     (etac (sym RS initsegI) 4),
     (rtac (Incomparable_LFO RS IncomparableD RS sym) 2),
     (etac (sym RS initsegI) 3),
     (REPEAT (ares_tac [domainI] 2)),
     (REPEAT (hyp_subst_tac 1)),
     (asm_full_simp_tac (IFOL_ss addsimps [app_right_inj_iff]) 1),
     (hyp_subst_tac 1),
     (etac (spec RS mp RS notE) 1),
     (REPEAT (atac 1)),
     (cut_facts_tac [prem] 2),
     (ALLGOALS (REPEAT o (eresolve_tac [LFO_E2, LFreeInE2]))),
     (REPEAT ((rtac (LOcc_domain RS subsetD RS SigmaD1) 1) THEN
            (atac 2) THEN
            (atac 1)))]);

qed_goal "LFreeForIn_lemma" LLambda.thy
    "[| !!y l m. [| LFreeIn(<l, TLVar(y)>, N); LFreeIn(<m, TLVar(x)>, M) |] \
\           ==> LFreeIn(<m @ l, TLVar(y)>, Lsubst(M, x, N)); \
\       N: LTerm; x: LVariable; M: LTerm\
\    |] ==> LFreeForIn(N, x, M)"
  (fn major::prems =>
    [(rtac LFreeForInI 1),
     (REPEAT (ares_tac prems 1)),
     (etac LFV_E 1),
     (forward_tac [major] 1),
     (atac 1),
     (eres_inst_tac [("l", "l @ la")] LFreeInE2 1),
     (cut_facts_tac prems 1),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs [LOcc_LsubstE, LFO_E2])),
     (REPEAT (etac LFreeInE2 1)),
     (eres_inst_tac [("x1", "x")] (TLVar_leaf RS conjE) 1),
     (rtac initseg_appI1 2),
     (atac 1),
     (etac initsegD2 1),
     (dtac initsegD2 1),
     ((dtac LOcc_typeD1 1) THEN (etac app_typeD 2)),
     (REPEAT (atac 1)),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs) 1),
     (etac app_appE 1),
     (etac initsegD2 1),
     ((etac LFreeInE2 1) THEN (etac LOcc_typeD1 1)),
     (atac 1),
     (safe_tac (ZF_cs addSEs [LFreeInE2])),
     (rtac (TLVar_leaf RS conjE) 2),
     (rtac initseg_appI1 4),
     ((atac 3) THEN (atac 2)),
     (dtac app_Nil_eqD1 5),
     (REPEAT ((atac 2) ORELSE (etac LOcc_typeD1 2))),
     (hyp_subst_tac 2),
    (* 30 *)
     ((etac (spec RS mp RS notE) 2) THEN (rtac LOcc_LsubstI1 2)),
     (atac 3),
     (etac initseg_appI3 5),
     ((dtac LOcc_typeD1 5) THEN (etac app_typeD 6)),
     (resolve_tac list.intrs 6),
     (safe_tac (ZF_cs addSEs [LFO_E] addSEs LTermOcc.Tag.free_SEs)),
    (* 36 *)
     (rtac (TLVar_leaf RS conjE) 1),
     (rtac initseg_appI1 3),
     ((atac 2) THEN (atac 1)),
     (dtac app_Nil_eqD1 4),
     (REPEAT ((atac 2) ORELSE (etac LOcc_typeD1 2))),
     (etac initsegD2 1),
     (hyp_subst_tac 1),
     ((etac (spec RS mp RS notE) 1) THEN (rtac LOcc_LsubstI1 1)),
     (atac 2),
     (etac initseg_appI3 4),
     (etac LOcc_typeD1 4),
     (safe_tac (ZF_cs addSEs [LFO_E] addSEs LTermOcc.Tag.free_SEs))]);

qed_goal "Lsubst_lemma" LLambda.thy
    "[| LFreeForIn(A, x, M); x ~: LFV(B); y ~= x; \
\       M: LTerm; A: LTerm; B: LTerm |] \
\      ==> Lsubst(Lsubst(M, x, A), y, B) = \
\                 Lsubst(Lsubst(M, y, B), x, Lsubst(A, y, B))"
  (fn major::prems =>
    [(cut_facts_tac prems 1),
     (subgoals_tac [("x ~= y")] 1),
     (fast_tac ZF_cs 2),
     (rtac (major RS rev_mp) 1),
     (LTermOcc.ind_tac "M" [] 1),
     (ALLGOALS (rtac impI)),
     (ALLGOALS (eresolve_tac LFreeForIn_LTermEs)),
     (TRYALL hyp_subst_tac),
     (ALLGOALS (asm_simp_tac LTerm_ss)),
     (ALLGOALS (excluded_middle_tac "y = xa")),
     (TRYALL hyp_subst_tac),
     (ALLGOALS (asm_simp_tac LTerm_ss)),
     (excluded_middle_tac "x = xa" 1),
     (subgoals_tac ["x ~: LFV(Lsubst(Ma, y, B))"] 3),
     (TRYALL hyp_subst_tac),
     (ALLGOALS (asm_simp_tac LTerm_ss)),
     (rtac notI 1),
     (etac LFV_E 1),
     (etac LFreeIn_LsubstE 1),
     (REPEAT (atac 1)),
     (REPEAT ((etac notE 1) THEN (etac LFV_I 1)))]);

qed_goal "Lsubst_lemma2" LLambda.thy
    "[| LFreeForIn(LVar(x), y, M); x ~: LFV(M); N: LTerm |] ==> \
\       Lsubst(Lsubst(M, y, LVar(x)), x, N) = Lsubst(M, y, N)"
  (fn major::sub::prems =>
    [(subgoals_tac ["M: LTerm", "x: LVariable", "y: LVariable"] 1),
     (REPEAT ((rtac (major RS LFreeForInE) 2) 
            THEN (eresolve_tac LTerm_typeEs 2) THEN (atac 2))),
     (cut_facts_tac prems 1),
     (rtac (sub RS rev_mp) 1),
     (rtac (major RS rev_mp) 1),
     (LTermOcc.ind_tac "M" [] 1),
     (ALLGOALS (asm_simp_tac LTerm_ss)),
     (safe_tac (ZF_cs addSEs LFreeForIn_LTermEs)),
     (TRYALL (eres_inst_tac [("R", "False")] notE)),
     (ALLGOALS (asm_simp_tac LTerm_ss)),
     (excluded_middle_tac "y = xa" 1),
     (subgoals_tac ["x ~= xa"] 3),
     (ALLGOALS (asm_full_simp_tac LTerm_ss)),
     (fast_tac ZF_cs 1)]);

qed_goal "Lsubst_lemma3" LLambda.thy
    "[| M: LTerm; A: LTerm; B: LTerm; y ~: LFV(A); x ~: LFV(B); x ~= y |] ==> \
\      Lsubst(Lsubst(M, x, A), y, B) = \
\             Lsubst(Lsubst(M, y, B), x, A)"
  (fn major::prems =>
    [(cut_facts_tac prems 1),
     (LTermOcc.ind_tac "M" [major] 1),
     (excluded_middle_tac "x = xa" 2),
     (excluded_middle_tac "y = xa" 3),
     (excluded_middle_tac "y = xa" 2),
     (excluded_middle_tac "x = xa" 1),
     (excluded_middle_tac "y = xa" 2),
     (excluded_middle_tac "y = xa" 1),
     (TRYALL hyp_subst_tac),
     (TRYALL (asm_full_simp_tac LTerm_ss))]);

qed_goal "Lsubst_lemma4" LLambda.thy
    "[| y ~: LFV(M) - {x}; LFreeForIn(A, x, M); B: LTerm |] ==> \
\      Lsubst(Lsubst(M, x, A), y, B) = Lsubst(M, x, Lsubst(A, y, B))"
  (fn sub::prem::prems =>
    [(cut_facts_tac ([prem RS LFreeForInD1] @ prems) 1),
     (rtac (sub RS rev_mp) 1),
     (rtac (prem RS rev_mp) 1),
     (LTermOcc.ind_tac "M" [prem RS LFreeForInD3] 1),
     (excluded_middle_tac "x = xa" 2),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_simp_tac LTerm_ss)),
     (safe_tac (ZF_cs addSEs LFreeForIn_LTermEs)),
     (ALLGOALS (asm_full_simp_tac LTerm_ss)),
     (etac swap 2),
     (etac swap 2),
     (etac swap 3),
     (etac swap 3),
     (excluded_middle_tac "y = xa" 1),
     (ALLGOALS (asm_full_simp_tac LTerm_ss))]);
