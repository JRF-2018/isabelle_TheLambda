(*
    File:        LBeta.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open LBeta;

qed_goalw "LBeta1_type1" LBeta.thy [LBeta1_def]
    "LBeta1(M, N) ==> M: LTerm"
  (fn [major] =>
    [(rtac (major RS conjunct1) 1)]);

qed_goalw "LBeta1_type2" LBeta.thy [LBeta1_def]
    "LBeta1(M, N) ==> N: LTerm"
  (fn [major] =>
    [(cut_facts_tac [major] 1),
     (safe_tac ZF_cs),
     (rtac (LTermOcc.use_thm def_Occinv_type) 1),
     (rtac Occ_Graft1_in_Occ_range 1),
     (etac LFreeForInE 2),
     (REPEAT (ares_tac [LOcc_in_Occ_range, Lsubst_type] 1)),
     (rewrite_goals_tac [LSub_def]),
     (etac RepFunE 1),
     (forward_tac [LOcc_domain RS subsetD] 1),
     (atac 1),
     (etac SigmaE 1),
     (hyp_subst_tac 1),
     (asm_full_simp_tac ZF_ss 1),
     (etac domainI 1)]);

qed_goalw "LBeta1_baseI" LBeta.thy [LBeta1_def]
    "LFreeForIn(B, x, A) ==> LBeta1(LApp(LLam(x, A), B), Lsubst(A, x, B))"
  (fn [major] =>
    [(rtac (major RS LFreeForInE) 1),
     (REPEAT (ares_tac ([conjI, bexI, exI, refl, major] @ LTerm.intrs) 1)),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps
                  [LTermOcc.use_thm def_Sub_rec]) 2),
     (rtac Occ_consI1 2),
     (asm_simp_tac (LTerm_ss addsimps [Occ_Graft1_Nil,
                                     LTermOcc.use_thm def_Occinv_Occ]) 1)]);

qed_goalw "LBeta1_LLamI" LBeta.thy [LBeta1_def]
    "[| LBeta1(M, M');  x: LVariable |] ==> LBeta1(LLam(x, M), LLam(x, M'))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (safe_tac ZF_cs),
     (REPEAT (ares_tac ([bexI, conjI, refl, exI] @ LTerm.intrs) 1)),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps
                  [LTermOcc.use_thm def_Sub_rec]) 2),
     (res_inst_tac [("a", "0")] Occ_consI2 2),
     (asm_simp_tac list_ss 2),
     (asm_simp_tac (nth_ss addsimps LTermOcc.Term_cons_eqns) 2),
     (subgoals_tac ["A: LTerm", "B: LTerm", "xa: LVariable",
                  "l: list(nat)",
                  "Occ_Graft1(LOcc(LLam(x, M)), \
                   \              Cons(0, l), LOcc(Lsubst(A, xa, B)))\
                  \        : Occ_range(LTag, LArity)"] 1),
     (rtac Occ_Graft1_in_Occ_range 2),
     (REPEAT (ares_tac ([LOcc_in_Occ_range, Lsubst_type] @ LTerm.intrs) 2)),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps
                  [LTermOcc.use_thm Occ_Term_cons]) 2),
     (SELECT_GOAL (rewrite_goals_tac [LSub_def]) 2),
     (etac RepFunE 2),
     (forward_tac [LOcc_domain RS subsetD] 2),
     (atac 2),
     (etac SigmaE 2),
     (hyp_subst_tac 2),
     (asm_full_simp_tac ZF_ss 2),
     (rtac (Occ_consI2 RS domainI) 2),
     (asm_simp_tac list_ss 2),
     (asm_simp_tac nth_ss 2),
     (etac ((LTermOcc.use_thm def_Sub_type) RS subsetD RS SigmaD1) 2),
     (atac 2),
     (REPEAT ((etac LFreeForInE 2) THEN (atac 2))),
     (asm_full_simp_tac (LTerm_Term_cons_ss
                         addsimps (map LTermOcc.use_thm 
                                   [Occ_Term_cons])) 1),
     (rtac (Occ_Graft1_Occ_cons_Cons RS ssubst) 1),
     (ALLGOALS (asm_simp_tac LTerm_Term_cons_ss)),
     (rtac ((LTermOcc.use_thm def_Occinv2) RS trans RS sym) 1),
     (res_inst_tac [("P", "%x. x: ?X")] subst 1),
     (atac 2),
     (rtac (Occ_Graft1_Occ_cons_Cons RS ssubst) 1),
     (ALLGOALS (asm_simp_tac (LTerm_ss addsimps 
                              [LTermOcc.use_thm def_Occinv_Occ]))),
     (REPEAT (ares_tac ([Occ_Graft1_domain, LOcc_domain, Lsubst_type, PowI]
                      @ list.intrs @ LTermOcc.Tag.intrs) 1))]);

qed_goalw "LBeta1_LAppI1" LBeta.thy [LBeta1_def]
    "[| LBeta1(A, A');  B: LTerm |] ==> LBeta1(LApp(A, B), LApp(A', B))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (safe_tac ZF_cs),
     (REPEAT (ares_tac ([bexI, conjI, refl, exI] @ LTerm.intrs) 1)),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps
                  [LTermOcc.use_thm def_Sub_rec]) 2),
     (res_inst_tac [("a", "0")] Occ_consI2 2),
     (asm_simp_tac list_ss 2),
     (REPEAT (ares_tac [succI1, succI2] 2)),
     (asm_simp_tac (nth_ss addsimps LTermOcc.Term_cons_eqns) 2),
     (subgoals_tac ["Aa: LTerm", "Ba: LTerm", "x: LVariable",
                  "l: list(nat)",
                  "Occ_Graft1(LOcc(LApp(A, B)), \
                   \              Cons(0, l), LOcc(Lsubst(Aa, x, Ba)))\
                  \        : Occ_range(LTag, LArity)"] 1),
     (rtac Occ_Graft1_in_Occ_range 2),
     (REPEAT (ares_tac ([LOcc_in_Occ_range, Lsubst_type] @ LTerm.intrs) 2)),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps
                  [LTermOcc.use_thm Occ_Term_cons]) 2),
     (SELECT_GOAL (rewrite_goals_tac [LSub_def]) 2),
     (etac RepFunE 2),
     (rtac (LOcc_domain RS subsetD RS SigmaE) 2),
     (atac 3),
     (atac 2),
     (hyp_subst_tac 2),
     (asm_full_simp_tac ZF_ss 2),
     (rtac (Occ_consI2 RS domainI) 2),
     (asm_simp_tac list_ss 2),
     (REPEAT (ares_tac [succI1, succI2] 2)),
     (asm_simp_tac nth_ss 2),
     (rtac ((LTermOcc.use_thm def_Sub_type) RS subsetD RS SigmaD1) 2),
     (atac 3),
     (atac 2),
     (REPEAT ((etac LFreeForInE 2) THEN (atac 2))),
     (asm_full_simp_tac (LTerm_Term_cons_ss
                  addsimps (map LTermOcc.use_thm 
                            [Occ_Term_cons])) 1),
     (rtac (Occ_Graft1_Occ_cons_Cons RS ssubst) 1),
     (ALLGOALS (asm_simp_tac LTerm_Term_cons_ss)),
     (rtac ((LTermOcc.use_thm def_Occinv2) RS trans RS sym) 1),
     (res_inst_tac [("P", "%x. x: ?X")] subst 1),
     (atac 2),
     (rtac (Occ_Graft1_Occ_cons_Cons RS ssubst) 1),
     (ALLGOALS (asm_simp_tac (LTerm_ss addsimps 
                            [LTermOcc.use_thm def_Occinv_Occ]))),
     (REPEAT (ares_tac ([Occ_Graft1_domain, LOcc_domain, Lsubst_type, PowI]
                      @ list.intrs @ LTermOcc.Tag.intrs) 1))]);

qed_goalw "LBeta1_LAppI2" LBeta.thy [LBeta1_def]
    "[| LBeta1(B, B');  A: LTerm |] ==> LBeta1(LApp(A, B), LApp(A, B'))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (safe_tac ZF_cs),
     (REPEAT (ares_tac ([bexI, conjI, refl, exI] @ LTerm.intrs) 1)),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps
                  [LTermOcc.use_thm def_Sub_rec]) 2),
     (res_inst_tac [("a", "1")] Occ_consI2 2),
     (asm_simp_tac list_ss 2),
     (asm_simp_tac (nth_ss addsimps LTermOcc.Term_cons_eqns) 2),
     (subgoals_tac ["Aa: LTerm", "Ba: LTerm", "x: LVariable",
                  "l: list(nat)",
                  "Occ_Graft1(LOcc(LApp(A, B)), \
                   \              Cons(1, l), LOcc(Lsubst(Aa, x, Ba)))\
                  \        : Occ_range(LTag, LArity)"] 1),
     (rtac Occ_Graft1_in_Occ_range 2),
     (REPEAT (ares_tac ([LOcc_in_Occ_range, Lsubst_type] @ LTerm.intrs) 2)),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps
                  [LTermOcc.use_thm Occ_Term_cons]) 2),
     (SELECT_GOAL (rewrite_goals_tac [LSub_def]) 2),
     (etac RepFunE 2),
     (rtac (LOcc_domain RS subsetD RS SigmaE) 2),
     (atac 3),
     (atac 2),
     (hyp_subst_tac 2),
     (asm_full_simp_tac ZF_ss 2),
     (rtac (Occ_consI2 RS domainI) 2),
     (asm_simp_tac list_ss 2),
     (asm_simp_tac nth_ss 2),
     (rtac ((LTermOcc.use_thm def_Sub_type) RS subsetD RS SigmaD1) 2),
     (atac 3),
     (atac 2),
     (REPEAT ((etac LFreeForInE 2) THEN (atac 2))),
     (asm_full_simp_tac (LTerm_Term_cons_ss
                  addsimps (map LTermOcc.use_thm 
                            [Occ_Term_cons])) 1),
     (rtac (Occ_Graft1_Occ_cons_Cons RS ssubst) 1),
     (ALLGOALS (asm_simp_tac LTerm_Term_cons_ss)),
     (rtac ((LTermOcc.use_thm def_Occinv2) RS trans RS sym) 1),
     (res_inst_tac [("P", "%x. x: ?X")] subst 1),
     (atac 2),
     (rtac (Occ_Graft1_Occ_cons_Cons RS ssubst) 1),
     (ALLGOALS (asm_simp_tac (LTerm_ss addsimps 
                            [LTermOcc.use_thm def_Occinv_Occ]))),
     (REPEAT (ares_tac ([Occ_Graft1_domain, LOcc_domain, Lsubst_type, PowI]
                      @ list.intrs @ LTermOcc.Tag.intrs) 1))]);

qed_goalw "LBeta1_LVarE" LBeta.thy [LBeta1_def]
    "LBeta1(LVar(x), N) ==> R"
  (fn [major] =>
    [(cut_facts_tac [major] 1),
     (safe_tac (ZF_cs addSEs LTerm_typeEs)),
     (rotate_tac 2 1),
     (asm_full_simp_tac (LTermOcc.Term_cons_ss addsimps
                       [LTermOcc.use_thm def_Sub_rec]) 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Term_cons_eqns) 1),
     (etac Occ_consE2 1),
     (asm_full_simp_tac list_ss 3),
     (safe_tac (ZF_cs addSEs LTerm.free_SEs addSIs list.intrs))]);

qed_goalw "LBeta1_LLamE" LBeta.thy [LBeta1_def]
    "[| LBeta1(LLam(x, M), N); \
\       !!N'. [| N = LLam(x, N'); LBeta1(M, N'); x: LVariable |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac ([conjE, bexE, exE] @ LTerm_typeEs) 1)),
     (rotate_tac 4 1),
     (bound_hyp_subst_tac 1),
     (asm_full_simp_tac (LTermOcc.Term_cons_ss addsimps
                       [LTermOcc.use_thm def_Sub_rec,
                        LTermOcc.use_thm Occ_Term_cons]) 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Term_cons_eqns) 1),
     (etac Occ_consE 1),
     (fast_tac (ZF_cs addSEs LTerm.free_SEs) 1),
     (asm_full_simp_tac list_ss 1),
     (etac succE 1),
     (etac emptyE 2),
     (etac conjE 1),
     (bound_hyp_subst_tac 1),
     (asm_full_simp_tac nth_ss 1),
    (* 14 *)
     (rtac prem 1),
     (etac trans 1),
     (REPEAT (ares_tac [conjI, refl, bexI, exI] 2)),
     (rtac (Occ_Graft1_Occ_cons_Cons RS ssubst) 1),
     (ALLGOALS (asm_simp_tac LTerm_ss)),
     (rtac (LTermOcc.use_thm def_Sub_type RS subsetD RS SigmaD1) 1),
     (atac 2),
     (atac 1),
     (subgoals_tac ["A: LTerm", "xa: LVariable", "B: LTerm",
                  "Occ_Graft1(LOcc(M), m, LOcc(Lsubst(A, xa, B))): \
                  \    Occ_range(LTag, LArity)",
                  "LOccinv(Occ_Graft1(LOcc(M), m, LOcc(Lsubst(A, xa, B)))): \
                  \     LTerm"] 1),
     (rtac Occ_Graft1_in_Occ_range 3),
     (REPEAT (ares_tac ([LOcc_in_Occ_range, Lsubst_type,
                       LTermOcc.use_thm def_Occinv_type] @ LTerm.intrs) 2)),
     (SELECT_GOAL (rewrite_goals_tac [LSub_def]) 2),
     (etac RepFunE 2),
     (rtac (LOcc_domain RS subsetD RS SigmaE) 2),
     (atac 3),
     (hyp_subst_tac 3),
     (asm_full_simp_tac ZF_ss 3),
     (etac domainI 3),
     (atac 2),
     (REPEAT ((etac LFreeForInE 2) THEN (atac 2))),
     (rtac trans 1),
     (rtac (LTermOcc.use_thm def_Occinv_Occ) 2),
     (res_inst_tac [("f", "LOccinv")] function_apply_eq 1),
     (ALLGOALS (asm_simp_tac (LTermOcc.Term_cons_ss
                            addsimps [LTermOcc.use_thm Occ_Term_cons,
                                      LTermOcc.use_thm def_Occ_Occinv])))]);

qed_goalw "LBeta1_LAppE" LBeta.thy [LBeta1_def]
    "[| LBeta1(LApp(A, B), N); \
\       !!x N'. [| A = LLam(x, N'); N = Lsubst(N', x, B); \
\               LFreeForIn(B, x, N') |] ==> R; \
\       !!A'. [| N = LApp(A',B); LBeta1(A, A'); B: LTerm |] ==> R; \
\       !!B'. [| N = LApp(A, B'); LBeta1(B, B'); A: LTerm |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac ([conjE, bexE, exE] @ LTerm_typeEs) 1)),
     (rotate_tac 4 1),
     (bound_hyp_subst_tac 1),
     (asm_full_simp_tac (LTermOcc.Term_cons_ss addsimps
                       [LTermOcc.use_thm def_Sub_rec,
                        LTermOcc.use_thm Occ_Term_cons]) 1),
     (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Term_cons_eqns) 1),
     (etac Occ_consE 1),
     (asm_full_simp_tac list_ss 2),
     (etac succE 2),
     (etac succE 3),
     (rtac prem2 3),
     (rtac prem3 2),
     (rtac prem1 1),
     (safe_tac (ZF_cs addSEs LTerm.free_SEs addSEs LTerm_typeEs)),
     (rtac refl 1),
     (rtac (Occ_Graft1_Nil RS ssubst) 1),
     (rtac Occ_cons_type 1),
     (resolve_tac LTermOcc.Tag.intrs 1),
     (REPEAT (ares_tac ([Occ_cons_type, PowI, LOcc_domain, 
                       Lsubst_type] @ list.intrs @ LTerm.intrs) 1)),
     (asm_simp_tac (LTerm_ss addsimps [LTermOcc.use_thm def_Occinv_Occ]) 1),
     (atac 1),
     (ALLGOALS (asm_full_simp_tac nth_ss)),
     (REPEAT (ares_tac [bexI, exI, conjI, refl] 2)),
     (REPEAT (ares_tac [bexI, exI, conjI, refl] 3)),
     (ALLGOALS (rtac (Occ_Graft1_Occ_cons_Cons RS ssubst))),
     (ALLGOALS (asm_simp_tac LTerm_ss)),
     (rtac (LTermOcc.use_thm def_Sub_type RS subsetD RS SigmaD1) 1),
     (atac 2),
     (atac 1),
     (rtac (LTermOcc.use_thm def_Sub_type RS subsetD RS SigmaD1) 2),
     (atac 3),
     (atac 2),
    (* 32 *)
     (subgoals_tac ["Aa: LTerm", "x: LVariable", "Ba: LTerm",
                  "Occ_Graft1(LOcc(A), m, LOcc(Lsubst(Aa, x, Ba))): \
                  \    Occ_range(LTag, LArity)",
                  "LOccinv(Occ_Graft1(LOcc(A), m, LOcc(Lsubst(Aa, x, Ba)))): \
                  \     LTerm"] 2),
     (subgoals_tac ["Aa: LTerm", "x: LVariable", "Ba: LTerm",
                  "Occ_Graft1(LOcc(B), m, LOcc(Lsubst(Aa, x, Ba))): \
                  \    Occ_range(LTag, LArity)",
                  "LOccinv(Occ_Graft1(LOcc(B), m, LOcc(Lsubst(Aa, x, Ba)))): \
                  \     LTerm"] 1),
     (rtac Occ_Graft1_in_Occ_range 3),
     (REPEAT (ares_tac ([LOcc_in_Occ_range, Lsubst_type,
                       LTermOcc.use_thm def_Occinv_type] @ LTerm.intrs) 2)),
     (SELECT_GOAL (rewrite_goals_tac [LSub_def]) 2),
     (etac RepFunE 2),
     (rtac (LOcc_domain RS subsetD RS SigmaE) 2),
     (atac 3),
     (hyp_subst_tac 3),
     (asm_full_simp_tac ZF_ss 3),
     (etac domainI 3),
     (atac 2),
     (REPEAT ((etac LFreeForInE 2) THEN (atac 2))),
     (rtac Occ_Graft1_in_Occ_range 4),
     (REPEAT (ares_tac ([LOcc_in_Occ_range, Lsubst_type,
                       LTermOcc.use_thm def_Occinv_type] @ LTerm.intrs) 3)),
     (SELECT_GOAL (rewrite_goals_tac [LSub_def]) 3),
     (etac RepFunE 3),
     (rtac (LOcc_domain RS subsetD RS SigmaE) 3),
     (atac 4),
     (hyp_subst_tac 4),
     (asm_full_simp_tac ZF_ss 4),
     (etac domainI 4),
     (atac 3),
     (REPEAT ((etac LFreeForInE 3) THEN (atac 3))),
     (rtac trans 2),
     (rtac (LTermOcc.use_thm def_Occinv_Occ) 3),
     (res_inst_tac [("f", "LOccinv")] function_apply_eq 2),
     (rtac trans 1),
     (rtac (LTermOcc.use_thm def_Occinv_Occ) 2),
     (res_inst_tac [("f", "LOccinv")] function_apply_eq 1),
     (ALLGOALS (asm_simp_tac (LTermOcc.Term_cons_ss
                            addsimps [LTermOcc.use_thm Occ_Term_cons,
                                      LTermOcc.use_thm def_Occ_Occinv])))]);

val LBeta1_LTermEs = [LBeta1_LVarE, LBeta1_LLamE, LBeta1_LAppE];

qed_goal "LBeta1_redex_lemma" LBeta.thy
    "[| Infinite(LVariable); \
\      M: LTerm; <l, LApp(LLam(x, A),B)>: LSub(M) |] ==> \
\      EX N A'. LAlpha(M, N) & <l, LApp(LLam(x, A'), B)>: LSub(N) & \
\               LFreeForIn(B, x, A')"
  (fn [infv, major, prem] =>
    [(rtac (prem RS rev_mp) 1),
     (res_inst_tac [("x", "l")] spec 1),
     (LTermOcc.ind_tac "M" [major] 1),
     (ALLGOALS (asm_simp_tac (LTermOcc.Term_cons_ss 
                            addsimps [LTermOcc.use_thm def_Sub_rec]))),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps LTermOcc.Term_cons_eqns))),
     (ALLGOALS ((rtac (impI RS allI)) THEN' (etac Occ_consE2))),
     (TRYALL (REPEAT o (ares_tac 
              ([LTermOcc.use_thm def_Sub_type RS PowI] @ list.intrs)))),
     (ALLGOALS (asm_full_simp_tac (list_ss addsimps [le_succ_iff]))),
     (safe_tac (ZF_cs addSEs LTerm.free_SEs addSEs LTerm_typeEs)),
     (ALLGOALS (asm_full_simp_tac nth_ss)),
     (rtac (infv RS Infinite_LVariable_LAlpha_lemma RS bexE) 2),
     (etac conjE 5),
     (rtac (conjI RS exI RS exI) 5),
     (rtac conjI 6),
     (atac 7),
     (rtac LAlpha_LAppI 5),
     (rtac LAlpha_LLamI1 5),
     (atac 5),
     (REPEAT (ares_tac [LAlpha_refl] 2)),
     (asm_simp_tac (LTermOcc.Term_cons_ss 
                  addsimps [LTermOcc.use_thm def_Sub_rec]) 2),
     (rtac Occ_consI1 2),
    (* 21 *)
     (ALLGOALS ((dtac (spec RS mp)) THEN' (atac))),
     (safe_tac ZF_cs),
     (ALLGOALS (rtac (conjI RS exI RS exI))),
     (TRYALL (REPEAT o (ares_tac [LAlpha_LLamI1, LAlpha_LAppI, LAlpha_refl]))),
     (ALLGOALS (fn i => (rtac conjI i) THEN (atac (i + 1)))),
     (ALLGOALS (forward_tac [LAlphaD1 RS LSkeltonEqD2])),
     (ALLGOALS (asm_simp_tac (LTermOcc.Term_cons_ss 
                            addsimps [LTermOcc.use_thm def_Sub_rec]))),
     (ALLGOALS (rtac Occ_consI2)),
     (ALLGOALS (asm_simp_tac (LTerm_ss addsimps LTermOcc.Term_cons_eqns)))]);

qed_goal "LFreeForIn_left_LsubstD1" LBeta.thy
    "[| LFreeForIn(Lsubst(A, x, B), y, M); LFreeForIn(LVar(x), y, M); \
\       LFreeForIn(B, x, A) \
\    |] ==> LFreeForIn(A, y, M)"
  (fn [major, prem1, prem2] =>
    [(cut_facts_tac ([prem1, prem2] RL 
                   [LFreeForInD1, LFreeForInD2, LFreeForInD3]) 1),
     (eresolve_tac LTerm_typeEs 1),
     (cut_facts_tac [prem2] 1),
     (rtac LFreeForInI 1),
     (etac LFV_E 4),
     (excluded_middle_tac "x = z" 4),
     (hyp_subst_tac 5),
     (rtac (major RS LFreeForInE) 4),
     (rtac (prem1 RS LFreeForInE) 5),
     (etac (spec RS spec RS spec RS mp) 5),
     (etac (spec RS spec RS spec RS mp) 4),
     (safe_tac ZF_cs),
     (asm_simp_tac LTerm_ss 5),
     (REPEAT (atac 2)),
     (rtac LFV_I 1),
     (rtac LFreeIn_LsubstI1 1),
     (REPEAT (atac 1))]);

qed_goal "LFreeForIn_right_LsubstD" LBeta.thy
    "[| LFreeForIn(A, x, Lsubst(M, y, B)); LFreeForIn(B, y, M); x: LFV(B) \
\    |] ==> LFreeForIn(A, y, M)"
  (fn [major, prem1, prem2] =>
    [(cut_facts_tac ([major, prem1] RL 
                   [LFreeForInD1, LFreeForInD2, LFreeForInD3]) 1),
     (rtac (prem2 RS LFV_E) 1),
     (excluded_middle_tac "y: LFV(M)" 1),
     (rtac LFreeForInI 1),
     ((etac notE 4) THEN (etac LFV_I 4)),
     (rtac LFreeForInI 4),
     (REPEAT (atac 1)),
     (REPEAT (etac LFV_E 1)),
     (rtac (major RS LFreeForInE) 1),
     (etac (spec RS spec RS spec RS mp) 1),
     (safe_tac ZF_cs),
     (etac LFV_I 1),
     (rtac LOcc_LsubstI1 2),
     (atac 3),
     (fast_tac (ZF_cs addSEs [LFO_E] addSEs LTermOcc.Tag.free_SEs) 2),
     (rtac LFreeIn_LsubstI2 1),
     (REPEAT (ares_tac [prem1, LFO_I] 1)),
     (etac initseg_appI3 1),
     ((etac LFreeInE2 1) THEN (etac LOcc_typeD1 1) THEN (atac 1))]);

qed_goal "LFreeIn_TLVar_leaf" LBeta.thy
    "[| LFreeIn(<l, T>, M); <l @ m, U>: LOcc(M) |] ==> m = [] & T = U"
  (fn [prem1, prem2] =>
    [(rtac (prem1 RS LFreeInE) 1),
     (forward_tac [prem2 RSN (2, TLVar_leaf)] 1),
     (safe_tac ZF_cs),
     (rtac initseg_appI1 1),
     (etac app_Nil_eqD1 3),
     (forward_tac [prem2 RS LOcc_typeD1] 2),
     (etac app_typeD 2),
     (REPEAT ((atac 1) ORELSE (etac LOcc_typeD1 1)))]);

qed_goal "LFreeForIn_right_LsubstI1" LBeta.thy
    "[| LFreeForIn(N, x, A); B: LTerm; x ~: LFV(B) |] ==> \
\        LFreeForIn(N, x, Lsubst(A, y, B))"
  (fn [prem1, prem2, prem3] =>
    [(cut_facts_tac ([prem1] RL 
                   [LFreeForInD1, LFreeForInD2, LFreeForInD3]) 1),
     (cut_facts_tac [prem2] 1),
     (REPEAT (ares_tac [Lsubst_type, LFreeForInI] 1)),
     (safe_tac (ZF_cs addSEs [LFreeIn_LsubstE, initseg_right_appE,
                            initseg_left_appE,
                            LOcc_LsubstE, LFV_E, LFO_E2]
              addSDs [sym RS app_Nil_eqD1])),
     (TRYALL ((etac LFreeInE2) THEN' (etac LOcc_typeD1) THEN' atac)),
     (TRYALL ((rtac (prem3 RS notE)) THEN' (etac LFV_I))),
     (((forward_tac [LFreeIn_TLVar_leaf]) THEN' 
     (etac LFreeInE2) THEN' atac) 2),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs) 2),
     (((rtac (prem1 RS LFreeForInE)) THEN'
     (etac (spec RS spec RS spec RS mp)) THEN'
     (REPEAT o (ares_tac [LFV_I, conjI, initseg_appI1]))) 1)]);

qed_goal "LFreeForIn_left_LsubstI" LBeta.thy
    "[| LFreeForIn(A, x, M); LFreeForIn(B, x, M) |] ==> \
\        LFreeForIn(Lsubst(A, y, B), x, M)"
  (fn [prem1, prem2] =>
    [(cut_facts_tac ([prem1, prem2] RL 
                   [LFreeForInD1, LFreeForInD2, LFreeForInD3]) 1),
     (REPEAT (ares_tac [Lsubst_type, LFreeForInI] 1)),
     (safe_tac (ZF_cs addSEs [LFreeIn_LsubstE, LFV_E])),
     (((rtac (prem1 RS LFreeForInE)) THEN'
     (etac (spec RS spec RS spec RS mp)) THEN'
     (REPEAT o (ares_tac [LFV_I, conjI, initseg_appI1]))) 1),
     (((rtac (prem2 RS LFreeForInE)) THEN'
     (etac (spec RS spec RS spec RS mp)) THEN'
     (REPEAT o (ares_tac [LFV_I, conjI, initseg_appI1]))) 1)]);

qed_goal "LBeta1_LsubstI" LBeta.thy
    "[| LBeta1(M, M'); LFreeForIn(N, x, M); LFreeForIn(N, x, M') |] \
\        ==> LBeta1(Lsubst(M, x, N), Lsubst(M', x, N))"
  (fn [major, prem1, prem2] =>
    [(rtac (prem2 RS rev_mp) 1),
     (rtac (prem1 RS rev_mp) 1),
     (rtac (major RS rev_mp) 1),
     (rtac (major RS LBeta1_type2 RSN (2, bspec)) 1),
     (LTermOcc.ind_tac "M" [major RS LBeta1_type1] 1),
     (safe_tac (ZF_cs addSEs LBeta1_LTermEs 
              addSEs LFreeForIn_LTermEs)),
     (subgoals_tac ["xaa ~= x"] 8),
     (fast_tac ZF_cs 9),
     (ALLGOALS (asm_full_simp_tac (LTerm_ss
                            addsimps [Lsubst_lemma, Lsubst_lemma4,
                                      LFreeForInD1, LFreeForInD3]))),
     (rtac LBeta1_LAppI2 10),
     (rtac LBeta1_LAppI1 9),
     (TRYALL (resolve_tac [LBeta1_LLamI, LBeta1_baseI])),
     (TRYALL (REPEAT o (ares_tac [Lsubst_type]))),
     (TRYALL (etac LFreeForInD1)),
     (ALLGOALS (asm_full_simp_tac (LTerm_ss
                            addsimps [LFreeForInD1, LFreeForInD3]))),
     (dtac (bspec RS mp RS mp RS mp) 2),
     (atac 3),
     (etac LFreeForInD3 2),
     (rtac LFreeForInI 2),
     ((etac notE 5) THEN (etac LFV_I 5)),
     (REPEAT (atac 2)),
     (asm_full_simp_tac (LTerm_ss addsimps [LFreeForInD1, LFreeForInD3]) 2),
     (dtac (bspec RS mp RS mp RS mp) 1),
     (atac 2),
     (etac LBeta1_type2 1),
     (rtac LFreeForInI 2),
     ((etac notE 5) THEN (etac LFV_I 5)),
     (etac LBeta1_type2 4),
     (etac LFreeForInD1 2),
     (REPEAT (atac 1)),
     (asm_full_simp_tac (LTerm_ss addsimps [LFreeForInD1, LBeta1_type2]) 1),
    (* 31 *)
     (rtac LFreeForIn_right_LsubstI1 2),
     (etac LFreeForInD1 3),
     (atac 3),
     (ALLGOALS (excluded_middle_tac "x: LFV(Na)")),
     (ALLGOALS (asm_simp_tac LTerm_ss)),
     (safe_tac (ZF_cs addSDs [LFreeForIn_right_LsubstD])),
     (REPEAT (ares_tac [LFreeForIn_left_LsubstI] 1))]);

(** LBV **)
qed_goalw "LBV_I" LBeta.thy [LBV_def]
    "[| <l, TLLam(x)>: LOcc(M); M: LTerm |] ==> x: LBV(M)"
  (fn [major, prem] =>
    [(resolve_tac ([[major, prem] MRS LOcc_typeD2] RL LTag_typeEs) 1),
     (fast_tac (ZF_cs addIs [major]) 1)]);

qed_goalw "LBV_E" LBeta.thy [LBV_def]
    "[| x: LBV(M); \
\       !!l. [| <l, TLLam(x)>: LOcc(M); x: LVariable |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS CollectE) 1),
     (fast_tac (ZF_cs addIs [prem]) 1)]);

qed_goal "LBV_LVar" LBeta.thy
    "x: LVariable ==> LBV(LVar(x)) = 0"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSEs [LBV_E] addIs [LBV_I]
                        addSIs LTerm.intrs
                        addSEs LOcc_LTermEs addIs LOcc_LTermIs
                        addSEs LTermOcc.Tag.free_SEs)))]);

qed_goal "LBV_LLam" LBeta.thy
    "[| x: LVariable; M: LTerm |] ==> LBV(LLam(x, M)) = cons(x, LBV(M))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSEs [LBV_E] addIs [LBV_I]
                        addSIs LTerm.intrs
                        addSEs LOcc_LTermEs addIs LOcc_LTermIs
                        addSEs LTermOcc.Tag.free_SEs)))]);

qed_goal "LBV_LApp" LBeta.thy
    "[| M: LTerm; N: LTerm |] ==> LBV(LApp(M, N)) = LBV(M) Un LBV(N)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSEs [LBV_E] addIs [LBV_I]
                        addSIs LTerm.intrs
                        addSEs LOcc_LTermEs addIs LOcc_LTermIs
                        addSEs LTermOcc.Tag.free_SEs)))]);

val LBV_eqns = [LBV_LVar, LBV_LLam, LBV_LApp];

qed_goal "LAV_eq_LFV_LBV" LBeta.thy
    "M: LTerm ==> LAV(M) = LFV(M) Un LBV(M)"
  (fn [major] =>
    [(LTermOcc.ind_tac "M" [major] 1),
     (ALLGOALS (asm_simp_tac (LTerm_ss addsimps LAV_eqns addsimps LBV_eqns))),
     (ALLGOALS (fast_tac eq_cs))]);

qed_goal "LBV_Lsubst1" LBeta.thy
    "[| M: LTerm; N: LTerm; x: LFV(M) |] ==> \
\         LBV(Lsubst(M, x, N)) = LBV(M) Un LBV(N)"
  (fn [major, prem1, prem2] =>
    [(cut_facts_tac [prem1] 1),
     (rtac (prem2 RS rev_mp) 1),
     (LTermOcc.ind_tac "M" [major] 1),
     (excluded_middle_tac "x: LFV(M)" 3),
     (excluded_middle_tac "x: LFV(Na)" 4),
     (ALLGOALS (asm_full_simp_tac (LTerm_ss addsimps LBV_eqns))),
     (ALLGOALS (fast_tac eq_cs))]);

qed_goal "LBV_Lsubst2" LBeta.thy
    "[| M: LTerm; N: LTerm |] ==> LBV(Lsubst(M, x, N)) <= LBV(M) Un LBV(N)"
  (fn [major, prem] =>
    [(cut_facts_tac [major, prem] 1),
     (excluded_middle_tac "x : LFV(M)" 1),
     (ALLGOALS (asm_simp_tac (LTerm_ss addsimps [LBV_Lsubst1]))),
     (rtac Un_upper1 1)]);

qed_goal "disjoint_LBV_LFV_imp_LFreeForIn" LBeta.thy
    "[| LBV(M) Int LFV(N) = 0; M: LTerm; N: LTerm; x: LVariable |] \
\        ==> LFreeForIn(N, x, M)"
  (fn major::prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (ares_tac [LFreeForInI] 1)),
     (rtac (major RS disjointE) 1),
     (REPEAT (ares_tac [LBV_I] 1))]);

qed_goal "LFV_Fin" LBeta.thy
    "M: LTerm ==> LFV(M): Fin(LVariable)"
  (fn [major] =>
    [(rtac Fin_subset 1),
     (REPEAT (ares_tac [LFV_subset_LAV, major, LAV_Fin] 1))]);

qed_goal "LBV_Fin" LBeta.thy
    "M: LTerm ==> LBV(M): Fin(LVariable)"
  (fn [major] =>
    [(rtac Fin_subset 1),
     (rtac (major RS LAV_Fin) 2),
     (rtac (major RS LAV_eq_LFV_LBV RS ssubst) 1),
     (rtac Un_upper2 1)]);

qed_goal "Infinite_LVariable_LAlpha_lemma3" LBeta.thy
    "[| Infinite(LVariable); M: LTerm; X: Fin(LVariable) |] ==> \
\        EX M'. LAlpha(M, M') & LBV(M') Int X = 0"
  (fn [infv, major, prem] =>
    [(LTermOcc.ind_tac "M" [major] 1),
     (rtac exI 1),
     (rtac (LAlpha_LVarI RS conjI) 1),
     (atac 1),
     (asm_simp_tac (ZF_ss addsimps LBV_eqns) 1),
     (safe_tac ZF_cs),
     (forward_tac [LAlphaD1 RS LSkeltonEqD2] 1),
     (res_inst_tac [("F", "X Un LAV(M') Un {x}")] (infv RS InfiniteE) 1),
     (REPEAT (ares_tac ([Fin_UnI, LAV_Fin, prem] @ Fin.intrs) 1)),
     (asm_full_simp_tac (ZF_ss addsimps [LAV_eq_LFV_LBV]) 1),
     (REPEAT (etac conjE 1)),
     (rtac (conjI RS exI) 1),
     (rtac LAlpha_LLamI3 1),
     (atac 3),
     (rtac disjoint_LBV_LFV_imp_LFreeForIn 2),
     (asm_simp_tac LTerm_ss 2),
     (rtac disjointI 2),
     (fast_tac ZF_cs 2),
     (REPEAT (ares_tac LTerm.intrs 1)),
     (excluded_middle_tac "x: LFV(M')" 1),
     (TRYALL (asm_simp_tac (LTerm_ss addsimps LBV_eqns
                          addsimps [LBV_Lsubst1]))),
     (rtac (cons_eq RS subst) 1),
     (rtac (cons_eq RS subst) 2),
     (rtac disjoint_UnI 1),
     (rtac disjoint_UnI 3),
     (rtac disjointI 1),
     (rtac disjointI 3),
     (TRYALL atac),
     (fast_tac ZF_cs 1),
     (fast_tac ZF_cs 1),
     (rtac (conjI RS exI) 1),
     (REPEAT (ares_tac [LAlpha_LAppI] 1)),
     (asm_simp_tac (LTerm_ss addsimps LBV_eqns
                  addsimps [LAlphaD1 RS LSkeltonEqD2]) 1),
     (REPEAT (ares_tac [disjoint_UnI] 1))]);

qed_goal "LBeta1_LBV_lemma" LBeta.thy
    "LBeta1(M, N) ==> LBV(N) <= LBV(M)"
  (fn [major] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (major RS LBeta1_type2 RSN (2, bspec)) 1),
     (LTermOcc.ind_tac "M" [major RS LBeta1_type1] 1),
     (safe_tac (ZF_cs addSEs LBeta1_LTermEs addSEs LTerm_typeEs)),
     (excluded_middle_tac "xb: LFV(N')" 2),
     (rotate_tac 5 2),
     (rotate_tac 6 3),
     (rotate_tac 5 4),
     (rotate_tac 5 5),
     (ALLGOALS (asm_full_simp_tac (LTerm_ss addsimps LBV_eqns
                                 addsimps [LBV_Lsubst1]))),
     (TRYALL ((dtac (bspec RS mp)) THEN' (etac LBeta1_type2) THEN' atac)),
     (safe_tac ZF_cs),
     (ALLGOALS ((swap_res_tac [subsetD]) THEN' atac THEN' atac))]);

qed_goal "LBeta1_LFV_lemma" LBeta.thy
    "LBeta1(M, N) ==> LFV(N) <= LFV(M)"
  (fn [major] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (major RS LBeta1_type2 RSN (2, bspec)) 1),
     (LTermOcc.ind_tac "M" [major RS LBeta1_type1] 1),
     (safe_tac (ZF_cs addSEs LBeta1_LTermEs addSEs LTerm_typeEs)),
     (rotate_tac 5 3),
     (rotate_tac 5 4),
     (ALLGOALS (asm_full_simp_tac LTerm_ss)),
     (TRYALL ((dtac (bspec RS mp)) THEN' (etac LBeta1_type2) THEN' atac)),
     (safe_tac (ZF_cs addSEs [LFV_E, LFreeIn_LsubstE] addSEs
                LTermOcc.Tag.free_SEs)),
     (TRYALL ((etac notE) THEN' (etac LFV_I))),
     (TRYALL ((swap_res_tac [subsetD]) THEN' atac THEN' (etac LFV_I))),
     (etac LFV_I 1)]);

qed_goal "LBeta1_LAlpha_parallel_lemma" LBeta.thy
    "[| Infinite(LVariable); LBeta1(M, N); X: Fin(LVariable) |] ==> \
\       EX M' N'. LAlpha(M, M') & LAlpha(N, N') & \
\           LBV(M') Int X = 0  & LBeta1(M', N')"
  (fn [infv, major, prem1] =>
    [(cut_facts_tac [prem1] 1),
     (rtac (major RS rev_mp) 1),
     (rtac (major RS LBeta1_type2 RSN (2, bspec)) 1),
     (LTermOcc.ind_tac "M" [major RS LBeta1_type1] 1),
     (safe_tac (ZF_cs addSEs LBeta1_LTermEs)),
     (forward_tac [LFreeForInD2] 2),
     (forward_tac [LFreeForInD3] 2),
     (res_inst_tac [("F", "X Un LFV(N')")] (infv RS InfiniteE) 2),
     (REPEAT (ares_tac [Fin_UnI, prem1, LFV_Fin] 2)),
     (cut_inst_tac [("M", "N"), ("X", "X")] 
    (infv RS Infinite_LVariable_LAlpha_lemma3) 2),
     (REPEAT (ares_tac [prem1] 2)),
     (etac exE 2),
     (etac conjE 2),
     (forward_tac [LAlphaD1 RS LSkeltonEqD2] 2),
     (cut_inst_tac [("M", "N'"), ("X", "X Un {xb} Un LFV(M')")] 
    (infv RS Infinite_LVariable_LAlpha_lemma3) 2),
     (REPEAT (ares_tac (Fin.intrs @ [Fin_UnI, prem1, LFV_Fin]) 2)),
     (etac exE 2),
     (asm_full_simp_tac (ZF_ss addsimps [disjoint_Un_iff2, 
                                       disjoint_cons_iff2]) 2),
     (REPEAT (etac conjE 2)),
     (forw_inst_tac [("N", "M'a")] (LAlphaD1 RS LSkeltonEqD2) 2),
    (* 20 *)
     (subgoals_tac ["xb ~: LFV(M'a)", "LFreeForIn(M', xb, M'a)",
                  "LFreeForIn(LVar(xb), xa, M'a)"] 2),
     (rtac disjoint_LBV_LFV_imp_LFreeForIn 3),
     (asm_full_simp_tac (LTerm_ss addsimps [disjoint_Un_iff2, 
                                          disjoint_cons_iff2]) 3),
     (REPEAT (ares_tac LTerm.intrs 3)),
     (etac (disjoint_LBV_LFV_imp_LFreeForIn) 3),
     (rtac notI 6),
     (etac LFV_E 6),
     ((dtac (LAlpha_sym RS LAlphaD2) 6) THEN (atac 6)),
     ((etac notE 6) THEN (etac LFV_I 6)),
     (REPEAT (atac 3)),
    (* 30 *)
     (rtac (conjI RS exI RS exI) 2),
     (rtac LAlpha_LAppI 2),
     (rtac LAlpha_LLamI3 2),
     (atac 3),
     (REPEAT (ares_tac [conjI] 2)),
     (rtac conjI 3),
     (rtac LBeta1_baseI 4),
     (excluded_middle_tac "xa : LFV(M'a)" 3),
     (asm_simp_tac (LTerm_ss addsimps LBV_eqns
                  addsimps [disjoint_Un_iff, disjoint_cons_iff]) 3),
     (asm_simp_tac (LTerm_ss addsimps LBV_eqns
                  addsimps [LBV_Lsubst1,
                            disjoint_Un_iff, disjoint_cons_iff]) 3),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_lemma2]) 2),
     (rtac LAlpha_LsubstI 2),
     (REPEAT ((ares_tac [LAlpha_LsubstI, LFreeForIn_name_change] 2) ORELSE
            (etac (disjoint_LBV_LFV_imp_LFreeForIn) 2))),
    (* 43 *)
     (ALLGOALS ((dtac (bspec RS mp)) THEN' (etac LBeta1_type2) THEN' atac)),
     (safe_tac ZF_cs),
     (forw_inst_tac [("N", "M'")] (LAlphaD1 RS LSkeltonEqD2) 1),
     (forw_inst_tac [("N", "N'a")] (LAlphaD1 RS LSkeltonEqD2) 1),
     (forw_inst_tac [("M", "N'")] (LAlphaD1 RS LSkeltonEqD1) 1),
     (res_inst_tac [("F", "X Un LBV(M') Un LBV(N'a) Un LFV(M') Un LFV(N'a)")] 
    (infv RS InfiniteE) 1),
     (REPEAT (ares_tac [Fin_UnI, prem1, LFV_Fin, LBV_Fin] 1)),
     (asm_full_simp_tac ZF_ss 1),
     (REPEAT (etac conjE 1)),
     (subgoals_tac ["LFreeForIn(LVar(xb), x, M')",
                  "LFreeForIn(LVar(xb), x, N'a)"] 1),
     (rtac disjoint_LBV_LFV_imp_LFreeForIn 3),
     (rtac disjoint_LBV_LFV_imp_LFreeForIn 2),
     (asm_full_simp_tac (LTerm_ss addsimps [disjoint_Un_iff2, 
                                          disjoint_cons_iff2]) 2),
     (asm_full_simp_tac (LTerm_ss addsimps [disjoint_Un_iff2, 
                                          disjoint_cons_iff2]) 5),
     (REPEAT (ares_tac LTerm.intrs 2)),
     (rtac (conjI RS exI RS exI) 1),
     (REPEAT (ares_tac [LAlpha_LLamI3, conjI] 1)),
     (excluded_middle_tac "x: LFV(M')" 1),
     (asm_full_simp_tac (LTerm_ss addsimps LBV_eqns
                       addsimps [disjoint_Un_iff, disjoint_cons_iff]) 1),
     (asm_full_simp_tac (LTerm_ss addsimps LBV_eqns
                       addsimps [LBV_Lsubst1,
                                 disjoint_Un_iff, disjoint_cons_iff]) 1),
     (REPEAT (ares_tac [LBeta1_LLamI, LBeta1_LsubstI] 1)),
    (* 65 *)
     (cut_inst_tac [("M", "N"), ("X", "X")] 
    (infv RS Infinite_LVariable_LAlpha_lemma3) 1),
     (REPEAT (ares_tac [prem1] 1)),
     (etac exE 1),
     (etac conjE 1),
     (rtac (exI RS exI) 1),
     (REPEAT (ares_tac [LAlpha_LAppI, conjI] 1)),
     (asm_full_simp_tac (LTerm_ss addsimps [LAlphaD1 RS LSkeltonEqD2,
                                          disjoint_Un_iff]
                       addsimps LBV_eqns) 1),
     (REPEAT (ares_tac [LBeta1_LAppI1] 1)),
     (etac (LAlphaD1 RS LSkeltonEqD2) 1),
     (cut_inst_tac [("M", "M"), ("X", "X")] 
    (infv RS Infinite_LVariable_LAlpha_lemma3) 1),
     (REPEAT (ares_tac [prem1] 1)),
     (etac exE 1),
     (etac conjE 1),
     (rtac (exI RS exI) 1),
     (REPEAT (ares_tac [LAlpha_LAppI, conjI] 1)),
     (asm_full_simp_tac (LTerm_ss addsimps [LAlphaD1 RS LSkeltonEqD2,
                                          disjoint_Un_iff]
                       addsimps LBV_eqns) 1),
     (REPEAT (ares_tac [LBeta1_LAppI2] 1)),
     (etac (LAlphaD1 RS LSkeltonEqD2) 1)]);

qed_goal "LBeta1_LAlpha_parallel" LBeta.thy
    "[| Infinite(LVariable); LBeta1(M, N); x: LVariable; X: LTerm |] ==> \
\       EX M' N'. LAlpha(M, M') & LAlpha(N, N') & \
\           LFreeForIn(X, x, M') & LFreeForIn(X, x, N') & LBeta1(M', N')"
  (fn [infv, major, prem1, prem2] =>
    [(cut_inst_tac [("X", "LFV(X)")] ([infv, major] MRS 
                                    LBeta1_LAlpha_parallel_lemma) 1),
     (rtac (prem2 RS LFV_Fin) 1),
     (REPEAT (eresolve_tac [exE, conjE] 1)),
     (REPEAT (ares_tac [exI, conjI] 1)),
     (REPEAT ((ares_tac [disjoint_LBV_LFV_imp_LFreeForIn,
                       prem1, prem2, conjI, disjoint_subset,
                       LBeta1_LBV_lemma, subset_refl] 1) ORELSE
            (etac (LAlphaD1 RS LSkeltonEqD2) 1)))]);
