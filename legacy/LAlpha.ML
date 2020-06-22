(*
    File:        LAlpha.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open LAlpha;

(** LAV **)
qed_goalw "LAV_I1" LAlpha.thy [LAV_def]
    "[| <l, TLVar(x)>: LOcc(M); M: LTerm |] ==> x: LAV(M)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (forward_tac [LOcc_typeD2] 1),
     (eresolve_tac LTag_typeEs 2),
     (fast_tac ZF_cs 2),
     (atac 1)]);

qed_goalw "LAV_I2" LAlpha.thy [LAV_def]
    "[| <l, TLLam(x)>: LOcc(M); M: LTerm |] ==> x: LAV(M)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (forward_tac [LOcc_typeD2] 1),
     (eresolve_tac LTag_typeEs 2),
     (fast_tac ZF_cs 2),
     (atac 1)]);

qed_goalw "LAV_E" LAlpha.thy [LAV_def]
    "[| x: LAV(M); \
\     !!l. [| <l, TLVar(x)>: LOcc(M); x: LVariable |] \
\         ==> R; \
\     !!l. [| <l, TLLam(x)>: LOcc(M); x: LVariable |] \
\         ==> R \
\    |] ==> R"
  (fn major::prems =>
    [(rtac (major RS CollectE) 1),
     (ALLGOALS (fast_tac (ZF_cs addIs prems)))]);

qed_goalw "LAV_LVar" LAlpha.thy [LAV_def]
    "x: LVariable ==> LAV(LVar(x)) = {x}"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSEs LOcc_LTermEs addIs LOcc_LTermIs
                        addSEs LTermOcc.Tag.free_SEs)))]);

qed_goalw "LAV_LLam" LAlpha.thy [LAV_def]
    "x: LVariable ==> LAV(LLam(x, M)) = cons(x, LAV(M))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSEs LOcc_LTermEs addIs LOcc_LTermIs
                        addSEs LTermOcc.Tag.free_SEs)))]);

qed_goalw "LAV_LApp" LAlpha.thy [LAV_def]
    "LAV(LApp(M, N)) = LAV(M) Un LAV(N)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSEs LOcc_LTermEs addIs LOcc_LTermIs
                        addSEs LTermOcc.Tag.free_SEs)))]);

val LAV_eqns = [LAV_LVar, LAV_LLam, LAV_LApp];
val LAlpha_ss = LTerm_ss addsimps LAV_eqns;

qed_goalw "LAV_Fin" LAlpha.thy [LAV_def]
    "M: LTerm ==> LAV(M): Fin(LVariable)"
  (fn [prem] =>
    [(rtac (prem RS (LTermOcc.use_thm Occ_ind_cond_Occ_FinI) RS Fin_induct) 1),
     (simp_tac ZF_ss 1),
     (resolve_tac Fin.intrs 1),
     (etac SigmaE 1),
     (etac LTermOcc.Tag.elim 1),
     (ALLGOALS hyp_subst_tac),
     (res_inst_tac [("P", "%x. x: ?X")] ssubst 1),
     (eresolve_tac Fin.intrs 2),
     (atac 2),
     (res_inst_tac [("P", "%x. x: ?X")] ssubst 2),
     (eresolve_tac Fin.intrs 3),
     (atac 3),
     (res_inst_tac [("P", "%x. x: ?X")] ssubst 3),
     (atac 4),
     (ALLGOALS (rtac equalityI)),
     (ALLGOALS (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs)))]);

qed_goal "LFV_subset_LAV" LAlpha.thy
    "M: LTerm ==> LFV(M) <= LAV(M)"
  (fn [prem] =>
    [(LTermOcc.ind_tac "M" [prem] 1),
     (ALLGOALS (asm_simp_tac LAlpha_ss)),
     (REPEAT (fast_tac ZF_cs 1))]);

(** LSkeltonEq **)
qed_goalw "LSkeltonEqD1" LAlpha.thy [LSkeltonEq_def]
    "LSkeltonEq(M, N) ==> M: LTerm"
  (fn [prem] =>
    [(rtac (prem RS conjunct1) 1)]);

qed_goalw "LSkeltonEqD2" LAlpha.thy [LSkeltonEq_def]
    "LSkeltonEq(M, N) ==> N: LTerm"
  (fn [prem] =>
    [(rtac (prem RS conjunct2 RS conjunct1) 1)]);

qed_goalw "LSkeltonEq_TLVarD" LAlpha.thy [LSkeltonEq_def]
    "[| LSkeltonEq(M, N); <l, TLVar(x)>: LOcc(M) |] \
\       ==> EX x. <l, TLVar(x)>: LOcc(N)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS conjunct2 RS conjunct1
          RS spec RS iffD1) 1),
     (rtac exI 1),
     (rtac prem 1)]);

qed_goalw "LSkeltonEq_TLLamD" LAlpha.thy [LSkeltonEq_def]
    "[| LSkeltonEq(M, N); <l, TLLam(x)>: LOcc(M) |] \
\       ==> EX x. <l, TLLam(x)>: LOcc(N)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS conjunct2 RS conjunct2 RS conjunct1
          RS spec RS iffD1) 1),
     (rtac exI 1),
     (rtac prem 1)]);

qed_goalw "LSkeltonEq_TLAppD" LAlpha.thy [LSkeltonEq_def]
    "[| LSkeltonEq(M, N); <l, TLApp>: LOcc(M) |] \
\       ==> <l, TLApp>: LOcc(N)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS conjunct2 RS conjunct2 RS conjunct2
          RS spec RS iffD1) 1),
     (rtac prem 1)]);

qed_goalw "LSkeltonEq_refl" LAlpha.thy [LSkeltonEq_def]
    "M: LTerm ==> LSkeltonEq(M, M)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (fast_tac ZF_cs 1)]);

qed_goalw "LSkeltonEq_sym" LAlpha.thy [LSkeltonEq_def]
    "LSkeltonEq(M, N) ==> LSkeltonEq(N, M)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT ((etac (spec RS iff_sym) 1) ORELSE
            (ares_tac [conjI, allI] 1)))]);

qed_goalw "LSkeltonEq_trans" LAlpha.thy [LSkeltonEq_def]
    "[| LSkeltonEq(M, N); LSkeltonEq(N, L) |] ==> LSkeltonEq(M, L)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT (((etac (spec RS iff_trans) 1) THEN (etac spec 1)) ORELSE
            (ares_tac [conjI, allI] 1)))]);

qed_goalw "LSkeltonEq_LVarI" LAlpha.thy [LSkeltonEq_def]
    "[| x: LVariable; y: LVariable |] ==> LSkeltonEq(LVar(x), LVar(y))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (ares_tac (LTerm.intrs @ [conjI]) 1)),
     (rtac conjI 2),
     (ALLGOALS (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
                        addSEs LOcc_LTermEs addIs LOcc_LTermIs
                        addIs [iffI])))]);

qed_goalw "LSkeltonEq_LLamI" LAlpha.thy [LSkeltonEq_def]
    "[| x: LVariable; y: LVariable;  LSkeltonEq(M, N) |] \
\       ==> LSkeltonEq(LLam(x, M), LLam(y, N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT (ares_tac (LTerm.intrs @ [conjI]) 1)),
     (rtac conjI 2),
     (ALLGOALS (rtac (iffI RS allI))),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs LOcc_LTermEs)),
     (TRYALL (((dtac (spec RS iffD1)) THEN'(etac exI)) ORELSE'
            ((dtac (spec RS iffD2)) THEN'(etac exI)))),
     (TRYALL (((dtac (spec RS iffD1)) THEN'(atac)) ORELSE'
            ((dtac (spec RS iffD2)) THEN'(atac)))),
     (TRYALL (etac exE)),
     (REPEAT (ares_tac ([exI] @ LOcc_LTermIs) 1))]);

qed_goalw "LSkeltonEq_LAppI" LAlpha.thy [LSkeltonEq_def]
    "[| LSkeltonEq(A, C); LSkeltonEq(B, D)|] \
\       ==> LSkeltonEq(LApp(A, B), LApp(C, D))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT (ares_tac (LTerm.intrs @ [conjI]) 1)),
     (rtac conjI 2),
     (ALLGOALS (rtac (iffI RS allI))),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs LOcc_LTermEs)),
     (TRYALL (((dtac (spec RS iffD1)) THEN'(etac exI)) ORELSE'
            ((dtac (spec RS iffD2)) THEN'(etac exI)))),
     (TRYALL (((dtac (spec RS iffD1)) THEN'(atac)) ORELSE'
            ((dtac (spec RS iffD2)) THEN'(atac)))),
     (TRYALL (etac exE)),
     (REPEAT (ares_tac ([exI] @ LOcc_LTermIs) 1))]);

val LSkeltonEq_LTermIs = [LSkeltonEq_LVarI, LSkeltonEq_LLamI,
                          LSkeltonEq_LAppI];

qed_goalw "LSkeltonEq_LVarE" LAlpha.thy [LSkeltonEq_def]
    "[| LSkeltonEq(LVar(x), N); \
\       !! y B. [| N = LVar(y); x: LVariable; y: LVariable |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac (LTerm_typeEs @ [conjE]) 1)),
     (subgoals_tac ["EX y: LVariable.  N = LVar(y)"] 1),
     (subgoals_tac ["EX y. <[], TLVar(y)>: LOcc(N)"] 2),
     (etac (spec RS iffD1) 3),
     (REPEAT (ares_tac ([exI] @ LOcc_LTermIs) 3)),
     (etac exE 2),
     (eres_inst_tac [("a", "N")] LTerm.elim 2),
     (hyp_subst_tac 3),
     (hyp_subst_tac 4),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs list.free_SEs
              addSEs LOcc_LTermEs) 3),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs list.free_SEs
              addSEs LOcc_LTermEs) 3),
     (REPEAT (ares_tac [bexI] 2)),
     (etac bexE 1),
     (rtac prem 1),
     (REPEAT (atac 1))]);

qed_goalw "LSkeltonEq_LLamE" LAlpha.thy [LSkeltonEq_def]
    "[| LSkeltonEq(LLam(x, A), N); \
\       !! y B. [| N = LLam(y, B); x: LVariable; y: LVariable; \
\         LSkeltonEq(A, B) |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac (LTerm_typeEs @ [conjE]) 1)),
     (subgoals_tac ["EX y: LVariable.  EX B: LTerm. N = LLam(y, B)"] 1),
     (subgoals_tac ["EX y. <[], TLLam(y)>: LOcc(N)"] 2),
     (etac (spec RS iffD1) 3),
     (REPEAT (ares_tac ([exI] @ LOcc_LTermIs) 3)),
     (etac exE 2),
     (eres_inst_tac [("a", "N")] LTerm.elim 2),
     (hyp_subst_tac 2),
     (hyp_subst_tac 4),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs LOcc_LTermEs) 2),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs list.free_SEs
              addSEs LOcc_LTermEs) 3),
     (REPEAT (ares_tac [bexI] 2)),
     (REPEAT (etac bexE 1)),
     (rtac prem 1),
     (REPEAT (atac 1)),
     (hyp_subst_tac 1),
     (ALLGOALS (REPEAT o (ares_tac [conjI]))),
     (rtac conjI 2),
     (ALLGOALS (rtac (iffI RS allI))),
     (TRYALL (etac exE)),
     (TRYALL ((dtac (spec RS iffD1)) THEN' (eresolve_tac LOcc_LTermIs))),
     (TRYALL ((dtac (spec RS iffD2)) THEN' (eresolve_tac LOcc_LTermIs))),
     (TRYALL ((dtac (spec RS iffD1)) THEN' 
            (eresolve_tac (LOcc_LTermIs RL [exI])))),
     (TRYALL ((dtac (spec RS iffD1)) THEN' 
            (eresolve_tac (LOcc_LTermIs RL [exI])))),
     (TRYALL ((dtac (spec RS iffD2)) THEN' 
            (eresolve_tac (LOcc_LTermIs RL [exI])))),
     (safe_tac (ZF_cs addSEs list.free_SEs
              addSEs LOcc_LTermEs
              addSEs LTermOcc.Tag.free_SEs)),
     (ALLGOALS (etac exI))]);

qed_goalw "LSkeltonEq_LAppE" LAlpha.thy [LSkeltonEq_def]
    "[| LSkeltonEq(LApp(A, B), N); \
\       !! C D. [| N = LApp(C, D); LSkeltonEq(A, C); LSkeltonEq(B, D) |] \
\             ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac (LTerm_typeEs @ [conjE]) 1)),
     (subgoals_tac ["EX C: LTerm.  EX D: LTerm. N = LApp(C, D)"] 1),
     (subgoals_tac ["<[], TLApp>: LOcc(N)"] 2),
     (etac (spec RS iffD1) 3),
     (REPEAT (ares_tac LOcc_LTermIs 3)),
     (eres_inst_tac [("a", "N")] LTerm.elim 2),
     (hyp_subst_tac 2),
     (hyp_subst_tac 3),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs LOcc_LTermEs) 2),
     (fast_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs list.free_SEs
              addSEs LOcc_LTermEs) 2),
     (REPEAT (ares_tac [bexI] 2)),
     (REPEAT (etac bexE 1)),
     (rtac prem 1),
     (atac 1),
     (ALLGOALS hyp_subst_tac),
     (ALLGOALS (REPEAT o (ares_tac [conjI]))),
     (TRYALL (rtac conjI)),
     (ALLGOALS (rtac (iffI RS allI))),
     (TRYALL (etac exE)),
     (TRYALL ((dtac (spec RS iffD1)) THEN' (eresolve_tac LOcc_LTermIs))),
     (TRYALL ((dtac (spec RS iffD2)) THEN' (eresolve_tac LOcc_LTermIs))),
     (TRYALL ((dtac (spec RS iffD1)) THEN' 
            (eresolve_tac (LOcc_LTermIs RL [exI])))),
     (TRYALL ((dtac (spec RS iffD1)) THEN' 
            (eresolve_tac (LOcc_LTermIs RL [exI])))),
     (TRYALL ((dtac (spec RS iffD2)) THEN' 
            (eresolve_tac (LOcc_LTermIs RL [exI])))),
     (safe_tac (ZF_cs addSEs list.free_SEs
              addSEs LOcc_LTermEs
              addSEs LTermOcc.Tag.free_SEs)),
     (ALLGOALS (etac exI))]);

val LSkeltonEq_LTermEs = [LSkeltonEq_LVarE, LSkeltonEq_LLamE,
                          LSkeltonEq_LAppE];

qed_goalw "LSkeltonEq_Lsubst_LVar" LAlpha.thy [LSkeltonEq_def, Lsubst_def, Lgraft_def]
    "[| M: LTerm; y: LVariable |] ==> LSkeltonEq(M, Lsubst(M, x, LVar(y)))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (subgoals_tac ["Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(LVar(y))): \
 \                    Occ_range(LTag, LArity)"] 1),
     (REPEAT (ares_tac (LTerm.intrs @ 
                      [LOcc_in_Occ_range, Incomparable_LFO,
                       domain_mono, LFO_subset_LOcc,
                       LTermOcc.use_thm Occ_Graft_in_Occ_range2]) 2)),
     (REPEAT (ares_tac [conjI, LTermOcc.use_thm def_Occinv_type] 1)),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps 
                            [LTermOcc.use_thm def_Occ_Occinv]))),
     (rtac conjI 2),
     (ALLGOALS (rtac (iffI RS allI))),
     (TRYALL (etac exE)),
     (res_inst_tac [("Q", "<l, TLVar(xa)>: LFO(x, M)")] 
    (excluded_middle RS disjE) 1),
     (safe_tac (ZF_cs addSEs LOcc_LTermEs
              addSEs LTermOcc.Tag.free_SEs
              addSEs [LOcc_domain RSN (2, Occ_GraftE),
                      Occ_ShiftE, LFO_E])),
     (etac LFreeInE2 4),
     (forward_tac [LOcc_domain RS subsetD RS SigmaD1] 4),
     (atac 4),
     (asm_simp_tac (IFOL_ss addsimps [app_right_Nil]) 4),
     (TRYALL (etac exI)),
     (TRYALL (rtac exI)),
     (rtac Occ_GraftI1 4),
     (rtac Occ_GraftI1 3),
     (rtac Occ_GraftI2 2),
     (rtac Occ_GraftI1 1),
     (TRYALL atac),
     (etac (LFO_I RS domainI) 2),
     (res_inst_tac [("P", "%x. <x, ?X>: ?Y")] (app_right_Nil RS subst) 2),
     (rtac Occ_ShiftI 3),
     (etac (LOcc_domain RS subsetD RS SigmaD1) 2),
     (REPEAT (ares_tac LOcc_LTermIs 2)),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs
              addSEs [LFO_E, LFreeInE2])),
     (ALLGOALS ((rtac (LOcc_in_Occ_range RS Occ_rangeE)) THEN' atac)),
     (ALLGOALS (subgoals_tac ["la = l"])),
     (TRYALL (etac DenseTree_CorrectArity_0D)),
     (TRYALL atac),
     (TRYALL (DEPTH_SOLVE_1 o 
            ((dres_inst_tac [("x", "TLVar(x)")] bspec) THEN'
             (etac (LOcc_domain RS subsetD RS SigmaD2)) THEN'
             atac THEN'
             (asm_full_simp_tac (IFOL_ss addsimps LTermOcc.Arity_eqns))))),
     (ALLGOALS hyp_subst_tac),
     (subgoals_tac ["TLApp = TLVar(x)"] 3),
     (subgoals_tac ["TLLam(xa) = TLVar(x)"] 2),
     (subgoals_tac ["TLVar(xa) = TLVar(x)"] 1),
     (TRYALL (etac functionalD)),
     (TRYALL atac),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs)),
     (etac notE 1),
     (rtac (LFreeInI RS LFO_I) 1),
     (etac (spec RS mp RS notE) 3),
     (REPEAT (atac 1))]);

(** LAlpha **)
qed_goalw "LAlphaD1" LAlpha.thy [LAlpha_def]
    "LAlpha(M, N) ==> LSkeltonEq(M, N)"
  (fn [prem] =>
    [(rtac (prem RS conjunct1) 1)]);

qed_goalw "LAlphaD2" LAlpha.thy [LAlpha_def]
    "[| LAlpha(M, N); LFreeIn(u, M) |] ==> LFreeIn(u, N)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS conjunct1 RS spec RS iffD1) 1),
     (rtac prem 1)]);

qed_goalw "LAlphaD3" LAlpha.thy [LAlpha_def]
    "[| LAlpha(M, N); LBoundBy(<l, T>, <m, U>, M) |] \
\       ==> EX x. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, N)"
  (fn [major, prem] =>
    [(cut_facts_tac [major RS conjunct2 RS conjunct2] 1),
     (dtac (spec RS spec RS iffD1) 1),
     (rtac (exI RS exI) 1),
     (rtac prem 1),
     (REPEAT (etac exE 1)),
     (rtac LBoundByE 1),
     (atac 1),
     (fast_tac ZF_cs 1)]);

qed_goalw "LAlphaI" LAlpha.thy [LAlpha_def]
    "[| LSkeltonEq(M, N); \
\        !! l x. LFreeIn(<l, TLVar(x)>, M) <-> LFreeIn(<l, TLVar(x)>, N); \
\        !! l m. (EX x. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, M))\
\                <-> (EX x. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, N)) \
\    |] ==> LAlpha(M, N)"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem1 RS conjI) 1),
     (safe_tac ZF_cs),
     (REPEAT ((rtac LFreeInE 1) THEN 
            (atac 1) THEN
            (hyp_subst_tac 1) THEN
            (eresolve_tac ([prem2] RL [iffD1, iffD2]) 1))),
     (ALLGOALS ((rtac LBoundByE) THEN' atac)),
     (safe_tac ZF_cs),
     (dtac (exI RS (prem3 RS iffD1)) 1),
     (dtac (exI RS (prem3 RS iffD2)) 2),
     (ALLGOALS (fast_tac ZF_cs))]);

qed_goal "LAlphaI2" LAlpha.thy
    "[|  M: LTerm; N: LTerm; \
\        !! l. (EX x. <l, TLLam(x)>: LOcc(M)) <-> \
\                             (EX x. <l, TLLam(x)>: LOcc(N)); \
\        !! l. <l, TLApp>: LOcc(M) <-> <l, TLApp>: LOcc(N); \
\        !! l x. LFreeIn(<l, TLVar(x)>, M) <-> LFreeIn(<l, TLVar(x)>, N); \
\        !! l m. (EX x. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, M))\
\                <-> (EX x. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, N)) \
\    |] ==> LAlpha(M, N)"
  (fn prems =>
    [(rtac LAlphaI 1),
     (REPEAT (ares_tac prems 2)),
     (rewrite_goals_tac [LSkeltonEq_def]),
     (REPEAT (ares_tac (prems @ [conjI]) 1)),
     (REPEAT (ares_tac (prems @ [allI, conjI]) 2)),
     (safe_tac ZF_cs),
     (ALLGOALS (dtac TLVar_free_or_bound)),
     (TRYALL (ares_tac prems)),
     (safe_tac (ZF_cs addSEs [LBoundInE, LBinding_imp_LBoundByE])),
     (TRYALL (dresolve_tac (prems RL [iffD1, iffD2]))),
     (TRYALL (dresolve_tac ([exI] RL (prems RL [iffD1, iffD2])))),
     (safe_tac (ZF_cs addSEs [LBoundByE2, LBindingE2, LFreeInE2])),
     (ALLGOALS (etac exI))]);

qed_goalw "LAlpha_refl" LAlpha.thy [LAlpha_def]
    "M: LTerm ==> LAlpha(M, M)"
  (fn [major] =>
    [(cut_facts_tac [major] 1),
     (fast_tac (ZF_cs addIs [LSkeltonEq_refl]) 1)]);

qed_goalw "LAlpha_sym" LAlpha.thy [LAlpha_def]
    "LAlpha(M, N) ==> LAlpha(N, M)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT ((etac LSkeltonEq_sym 1) ORELSE
              (etac (spec RS iff_sym) 1) ORELSE
              (etac (spec RS spec RS iff_sym) 1) ORELSE
              (ares_tac [conjI, allI] 1)))]);

qed_goalw "LAlpha_trans" LAlpha.thy [LAlpha_def]
    "[| LAlpha(M, N); LAlpha(N, L) |] ==> LAlpha(M, L)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT (((etac LSkeltonEq_trans 1) THEN (atac 1)) ORELSE
              ((etac (spec RS iff_trans) 1) THEN (etac spec 1)) ORELSE
              ((etac (spec RS spec RS iff_trans) 1) THEN 
               (etac (spec RS spec) 1)) ORELSE
              (ares_tac [conjI, allI] 1)))]);

qed_goal "LAlpha_LVarI" LAlpha.thy
    "x: LVariable ==> LAlpha(LVar(x), LVar(x))"
  (fn [prem] =>
    [(rtac LAlpha_refl 1),
     (resolve_tac LTerm.intrs 1),
     (rtac prem 1)]);

qed_goalw "LAlpha_LLamI1" LAlpha.thy [LAlpha_def]
    "[| LAlpha(M, N); x: LVariable |] \
\        ==> LAlpha(LLam(x, M), LLam(x, N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (forward_tac [LSkeltonEqD1] 1),
     (forward_tac [LSkeltonEqD2] 1),
     (REPEAT (ares_tac [LSkeltonEq_LLamI, conjI] 1)),
     (rtac (iffI RS allI) 1),
     (eresolve_tac LFreeIn_LTermEs 2),
     (eresolve_tac LFreeIn_LTermEs 1),
     ((dtac (spec RS iffD1) 1) THEN (atac 1)),
     ((dtac (spec RS iffD2) 2) THEN (atac 2)),
     (TRYALL hyp_subst_tac),
     (REPEAT (((etac notE 1) THEN (etac sym 1)) ORELSE
              (ares_tac (LFreeIn_LTermIs @ [notI]) 1))),
     (rtac (iffI RS allI RS allI) 1),
     (safe_tac (ZF_cs addSEs LBoundBy_LTermEs
                addSEs LTermOcc.Tag.free_SEs)),
     ((dtac (spec RS iffD1) 1) THEN (atac 1)),
     ((dtac (spec RS iffD2) 3) THEN (atac 3)),
     ((dtac (spec RS spec RS iffD1) 2) THEN (etac (exI RS exI) 2)),
     ((dtac (spec RS spec RS iffD2) 4) THEN (etac (exI RS exI) 4)),
     (TRYALL (REPEAT o (etac exE))),
     (REPEAT (ares_tac (LBoundBy_LTermIs @ [exI]) 1))]);

qed_goalw "LAlpha_LLamI2" LAlpha.thy [LAlpha_def]
    "[| LAlpha(M, Lsubst(N, y, LVar(x))); LFreeForIn(LVar(x), y, N); \
\      x ~: LFV(N) |] \
\        ==> LAlpha(LLam(x, M), LLam(y, N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (subgoals_tac ["x: LVariable", "y: LVariable", "N: LTerm"] 1),
     (REPEAT ((etac LFreeForInE 2) THEN (eresolve_tac LTerm_typeEs 2)
              THEN (atac 2))),
     (rtac conjI 1),
     (rtac LSkeltonEq_LLamI 1),
     (REPEAT (atac 1)),
     (rtac LSkeltonEq_trans 1),
     (rtac (LSkeltonEq_Lsubst_LVar RS LSkeltonEq_sym) 2),
     (REPEAT (atac 1)),
    (**)
     (forward_tac [LSkeltonEqD1] 1),
     (rtac conjI 1),
     (rtac (iffI RS allI RS allI) 2),
     (rtac (iffI RS allI) 1),
     (safe_tac (ZF_cs addSEs LBoundBy_LTermEs
              addSEs LFreeIn_LTermEs)),
     (subgoals_tac ["x ~= ya"] 2),
     (rtac notI 3),
     (hyp_subst_tac 3),
     ((etac notE 3) THEN (etac LFV_I 3)),
     (dtac LFreeIn_LsubstI1 2),
     (REPEAT (atac 2)),
     ((dtac (spec RS iffD2) 2) THEN (atac 2)),
    (**)
     (subgoals_tac ["ma: list(nat)",
                  "LFreeIn(<ma @ [], TLVar(x)>, Lsubst(N, y, LVar(x)))"] 5),
     (etac LFreeInE2 7),
     (rtac (LOcc_domain RS subsetD RS SigmaD1) 7),
     (atac 8),
     (rtac LFreeIn_LsubstI2 6),
     (REPEAT (ares_tac [sub, LFreeIn_LVarI, LFO_I] 6)),
     (asm_full_simp_tac (IFOL_ss addsimps [app_right_Nil]) 5),
     ((dtac (spec RS iffD2) 5) THEN (atac 5)),
    (**)
     (dtac LBoundBy_LsubstI1 6),
     ((dtac (spec RS spec RS iffD2) 7) THEN (etac (exI RS exI) 7)),
     (REPEAT (ares_tac LTerm.intrs 6)),
    (**)
     ((dtac (spec RS iffD1) 1) THEN (atac 1)),
     ((dtac (spec RS iffD1) 3) THEN (atac 3)),
     ((dtac (spec RS spec RS iffD1) 4) THEN (etac (exI RS exI) 4)),
    (**)
     (TRYALL (REPEAT o (etac exE))),
     (forw_inst_tac [("u", "<ma, Ta>")] LBoundByD1 4),
     (etac LBindingE 4),
     (safe_tac (ZF_cs addSEs LFreeIn_LTermEs addSEs [LFO_E2]
              addSEs LBoundBy_LTermEs
              addSEs LTermOcc.Tag.free_SEs
              addSEs [LFreeIn_LsubstE, 
                      LBoundBy_LsubstE])),
     (TRYALL (atac ORELSE' (eresolve_tac LTerm.intrs))),
     (TRYALL (rtac (exI RS exI))),
     (ALLGOALS (resolve_tac (LFreeIn_LTermIs @ LBoundBy_LTermIs))),
     (TRYALL atac),
     (subgoals_tac ["n: list(nat)"] 4),
     (asm_simp_tac (IFOL_ss addsimps [app_right_Nil]) 4),
     (REPEAT (etac LFreeInE2 4)),
     (rtac (LOcc_domain RS subsetD RS SigmaD1) 4),
     (atac 5),
     (atac 4),
     (TRYALL (rtac notI)),
     (TRYALL hyp_subst_tac),
     (REPEAT ((etac notE 1) THEN ((rtac refl 1) ORELSE (etac LFV_I 1))))]);

qed_goalw "LAlpha_LAppI" LAlpha.thy [LAlpha_def]
    "[| LAlpha(A, C); LAlpha(B, D) |] ==> LAlpha(LApp(A, B), LApp(C, D))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (rtac conjI 1),
     (etac LSkeltonEq_LAppI 1),
     (atac 1),
     (subgoals_tac ["A: LTerm", "B: LTerm", "C: LTerm", "D: LTerm"] 1),
     (REPEAT (eresolve_tac [LSkeltonEqD1, LSkeltonEqD2] 2)),
     (rtac conjI 1),
     (rtac (iffI RS allI RS allI) 2),
     (rtac (iffI RS allI) 1),
     (safe_tac (ZF_cs addSEs LFreeIn_LTermEs
              addSEs LBoundBy_LTermEs)),
     ((dtac (spec RS iffD1) 1) THEN (atac 1)),
     ((dtac (spec RS iffD1) 2) THEN (atac 2)),
     ((dtac (spec RS iffD2) 3) THEN (atac 3)),
     ((dtac (spec RS iffD2) 4) THEN (atac 4)),
     ((dtac (spec RS spec RS iffD1) 5) THEN (etac (exI RS exI) 5)),
     ((dtac (spec RS spec RS iffD1) 6) THEN (etac (exI RS exI) 6)),
     ((dtac (spec RS spec RS iffD2) 7) THEN (etac (exI RS exI) 7)),
     ((dtac (spec RS spec RS iffD2) 8) THEN (etac (exI RS exI) 8)),
     (TRYALL (REPEAT o (etac exE))),
     (TRYALL (rtac (exI RS exI))),
     (ALLGOALS (resolve_tac (LFreeIn_LTermIs @ LBoundBy_LTermIs))),
     (TRYALL atac)]);

val LAlpha_LTermIs = [LAlpha_LVarI, LAlpha_LLamI1, 
                      LAlpha_LLamI2, LAlpha_LAppI];

qed_goal "LFreeForIn_name_change" LAlpha.thy
    "[| LFreeForIn(LVar(y), x, M); LFreeForIn(N, x, M); y ~: LFV(M) |] ==> \
\        LFreeForIn(N, y, Lsubst(M, x, LVar(y)))"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem1 RS LFreeForInE) 1),
     (rtac (prem2 RS LFreeForInE) 1),
     (cut_facts_tac [prem3] 1),
     (rtac LFreeForInI 1),
     (safe_tac (ZF_cs addSEs LTerm_typeEs 
              addSEs [LOcc_LsubstE, LFreeIn_LsubstE, LFO_E]
              addSIs [Lsubst_type] addSIs LTerm.intrs
              addSEs LOcc_LTermEs addSEs LTermOcc.Tag.free_SEs
              addSEs LFreeIn_LTermEs)),
     ((etac notE 1) THEN (etac LFV_I 1)),
     ((etac (spec RS spec RS spec RS mp) 1) THEN (etac conjI 1)),
     (safe_tac ZF_cs),
     (atac 3),
     (subgoals_tac ["n: list(nat)"] 1),
     (etac LFreeInE2 2),
     (etac LOcc_typeD1 2),
     (asm_simp_tac (IFOL_ss addsimps [app_right_Nil]) 1),
     (REPEAT (atac 1))]);

qed_goal "LFV_Lsubst_notI" LAlpha.thy
    "[| x ~= y; x: LVariable; M: LTerm |] \
\        ==> y ~: LFV(Lsubst(M, y, LVar(x)))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac notI 1),
     (safe_tac (ZF_cs addSEs [LFreeIn_LsubstE, LFO_E, LFV_E] 
              addSEs LFreeIn_LTermEs addSEs LTermOcc.Tag.free_SEs
              addSIs LTerm.intrs))]);

qed_goal "LAlpha_LLamI3" LAlpha.thy
    "[| LAlpha(M, N); LFreeForIn(LVar(y), x, N); y ~: LFV(N) |] \
\        ==> LAlpha(LLam(x, M), LLam(y, Lsubst(N, x, LVar(y))))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (forward_tac [LFreeForInD1] 1),
     (eresolve_tac LTerm_typeEs 1),
     (forward_tac [LFreeForInD2] 1),
     (forward_tac [LAlphaD1 RS LSkeltonEqD2] 1),
     (excluded_middle_tac "y = x" 1),
     (hyp_subst_tac 2),
     (rtac LAlpha_LLamI1 2),
     (asm_full_simp_tac (LTerm_ss addsimps [Lsubst_self]) 2),
     (rtac LAlpha_LLamI2 1),
     (asm_full_simp_tac (LTerm_ss addsimps 
                       [Lsubst_lemma2, Lsubst_self]) 1),
     (REPEAT (ares_tac [LFV_Lsubst_notI,
                      LFreeForIn_left_LVarI,
                      LFreeForIn_name_change] 1))]);

qed_goal "Infinite_LVariable_LAlpha_lemma" LAlpha.thy
    "[| Infinite(LVariable); M: LTerm; x: LVariable; N: LTerm |] ==> \
\        EX M': LTerm. LAlpha(M, M') & LFreeForIn(N, x, M')"
  (fn infv::major::prems =>
    [(cut_facts_tac prems 1),
     (LTermOcc.ind_tac "M" [major] 1),
     (rtac bexI 1),
     (REPEAT (ares_tac (LAlpha_LTermIs @ LFreeForIn_LTermIs
                      @ LTerm.intrs @ [conjI]) 1)),
     (safe_tac ZF_cs),
     (res_inst_tac [("F", "cons(xa, LAV(N) Un  LAV(M'))")] 
      (infv RS InfiniteE) 1),
     (REPEAT (ares_tac (Fin.intrs @ [LAV_Fin, Fin_UnI]) 1)),
     (res_inst_tac [("x", "LLam(xaa, Lsubst(M', xa, LVar(xaa)))")] bexI 1),
     (REPEAT (ares_tac (LTerm.intrs @ [Lsubst_type]) 2)),
     (subgoals_tac ["xaa ~: LFV(M')", "LFreeForIn(LVar(xaa), xa, M')"] 1),
     (safe_tac ZF_cs),
     (fast_tac (ZF_cs addIs [LFV_subset_LAV RS subsetD]) 4),
     (swap_res_tac [LFreeForInI] 3),
     (fast_tac (ZF_cs addSEs [LFV_E] addSEs LFreeIn_LTermEs 
              addSEs LTermOcc.Tag.free_SEs
              addIs [LAV_I2]) 6),
     (rtac LAlpha_LLamI2 1),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_self, Lsubst_lemma2]) 1),
     (rtac LFreeForIn_name_change 1),
     (rtac LFV_Lsubst_notI 4),
     (REPEAT (ares_tac [LFreeForIn_left_LVarI] 1)),
     (rtac LFreeForInI 1),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs [LFV_E, LFreeIn_LsubstE, LFO_E2,
                                         LFreeForInE, LOcc_LsubstE, 
                                         initseg_left_ConsE]
                           addSEs list.free_SEs
                           addSEs LOcc_LTermEs
                           addSEs LFreeIn_LTermEs 
                           addSEs LTermOcc.Tag.free_SEs)) 4),
     (REPEAT (etac LFreeInE2 4)),
     ((etac notE 4) THEN (etac LAV_I1 4)),
     ((etac (spec RS spec RS spec RS mp) 5) THEN (rtac conjI 5) THEN
    (rtac conjI 6) THEN (atac 6)),
     (REPEAT (ares_tac ([conjI, Lsubst_type, bexI, LFV_I] @ LAlpha_LTermIs 
                      @ LFreeForIn_LTermIs @ LTerm.intrs) 1))]);

qed_goal "Infinite_LVariable_LAlpha_lemma2" LAlpha.thy
    "[| Infinite(LVariable); M: LTerm; x: LVariable; X: Fin(LTerm) |] ==> \
\        EX M': LTerm. LAlpha(M, M') & (ALL N: X. LFreeForIn(N, x, M'))"
  (fn infv::major::prems =>
    [(cut_facts_tac prems 1),
     (LTermOcc.ind_tac "M" [major] 1),
     (rtac bexI 1),
     (REPEAT ((ares_tac (LAlpha_LTermIs @ LFreeForIn_LTermIs
                         @ LTerm.intrs @ [conjI, ballI]) 1) ORELSE
               ((dtac (Fin.dom_subset RS subsetD RS PowD) 1) THEN
                (etac subsetD 1)))),
     (safe_tac ZF_cs),
     (res_inst_tac [("F", "cons(xa, (UN N: X. LAV(N)) Un  LAV(M'))")] 
      (infv RS InfiniteE) 1),
     (REPEAT (ares_tac (Fin.intrs @ [LAV_Fin, Fin_UnI,
                                     Fin_UnionI, Fin_RepFunI]) 1)),
    (* 7 *)
     (res_inst_tac [("x", "LLam(xaa, Lsubst(M', xa, LVar(xaa)))")] bexI 1),
     (REPEAT (ares_tac (LTerm.intrs @ [Lsubst_type]) 2)),
     (subgoals_tac ["xaa ~: LFV(M')", "LFreeForIn(LVar(xaa), xa, M')"] 1),
     (safe_tac ZF_cs),
     (fast_tac (ZF_cs addIs [LFV_subset_LAV RS subsetD]) 4),
     (swap_res_tac [LFreeForInI] 3),
     (fast_tac (ZF_cs addSEs [LFV_E] addSEs LFreeIn_LTermEs 
              addSEs LTermOcc.Tag.free_SEs
              addIs [LAV_I2]) 6),
     (rtac LAlpha_LLamI2 1),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_self, Lsubst_lemma2]) 1),
     (rtac LFreeForIn_name_change 1),
     (rtac LFV_Lsubst_notI 4),
     (REPEAT (ares_tac [LFreeForIn_left_LVarI] 1)),
    (* 19 *)
     (rtac LFreeForInI 1),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs [LFV_E, LFreeIn_LsubstE, LFO_E2,
                                         LFreeForInE, LOcc_LsubstE, 
                                         initseg_left_ConsE]
                           addSEs list.free_SEs
                           addSEs LOcc_LTermEs
                           addSEs LFreeIn_LTermEs 
                           addSEs LTermOcc.Tag.free_SEs)) 4),
     (REPEAT (etac LFreeInE2 4)),
     (swap_res_tac [UnionI] 4),
     (rtac RepFunI 4),
     (atac 4),
     (etac LAV_I1 4),
     ((dtac bspec 5) THEN (atac 5)),
     (etac LFreeForInE 5),
     ((etac (spec RS spec RS spec RS mp) 5) THEN (rtac conjI 5) THEN
    (rtac conjI 6) THEN (atac 6)),
     (REPEAT ((ares_tac ([conjI, Lsubst_type, bexI, LFV_I, 
                          ballI] @ LAlpha_LTermIs 
                         @ LFreeForIn_LTermIs @ LTerm.intrs) 1) ORELSE
               ((dtac (Fin.dom_subset RS subsetD RS PowD) 1) THEN
                (etac subsetD 1)) ORELSE
               (etac bspec 1)))]);

qed_goalw "LAlpha_LVarE" LAlpha.thy [LAlpha_def]
    "[| LAlpha(LVar(x), N); \
\       [| N = LVar(x); x: LVariable |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (rtac prem 1),
     (safe_tac (ZF_cs addSEs [LSkeltonEq_LVarE])),
     (dtac (spec RS iffD1) 1),
     (resolve_tac LFreeIn_LTermIs 1),
     (eresolve_tac LFreeIn_LTermEs 2),
     (safe_tac (ZF_cs addSEs LTermOcc.Tag.free_SEs))]);

qed_goal "LAlpha_LLamE" LAlpha.thy
    "[| Infinite(LVariable); \
\       LAlpha(LLam(x, M), N); \
\       !! N'. [| N = LLam(x, N'); LAlpha(M, N') |] ==> R; \
\       !! y M' N'. [| N = LLam(y, N'); LAlpha(M, M'); \
\                    LFreeForIn(LVar(y), x, M'); y ~: LFV(M'); \
\                    LAlpha(N', Lsubst(M', x, LVar(y))) \
\       |] ==> R \
\    |] ==> R"
  (fn [infv, major, prem1, prem2] =>
    [(cut_facts_tac [major] 1),
     (rewrite_goals_tac [LAlpha_def]),
     (safe_tac ZF_cs),
     (etac LSkeltonEq_LLamE 1),
     (forward_tac [LSkeltonEqD1] 1),
     (forward_tac [LSkeltonEqD2] 1),
     (excluded_middle_tac "x = y" 1),
     (bound_hyp_subst_tac 2),
     (rtac prem1 2),
     (res_inst_tac [("M1", "M"), ("N1", "LVar(y)"), ("x1", "x")]
    (infv RS Infinite_LVariable_LAlpha_lemma RS bexE) 1),
     (REPEAT (ares_tac LTerm.intrs 1)),
     (etac conjE 1),
     (rtac prem2 1),
     (TRYALL atac),
     (TRYALL hyp_subst_tac),
     (rewrite_goals_tac [LAlpha_def]),
     (safe_tac (ZF_cs addSEs [LFV_E])),
     ((dtac (spec RS iffD2) 1) THEN (atac 1)),
     ((dtac (spec RS iffD1) 1) THEN (rtac LFreeIn_LLamI 1)),
     (atac 1),
     (safe_tac (ZF_cs addSEs LFreeIn_LTermEs
              addSEs LTermOcc.Tag.free_SEs)),
     (etac (LSkeltonEq_sym RS LSkeltonEq_trans) 1),
     (etac LSkeltonEq_trans 1),
     (REPEAT (ares_tac [LSkeltonEq_Lsubst_LVar] 1)),
    (**)
     (rtac LFreeInE 1),
     (atac 1),
     (hyp_subst_tac 1),
     (excluded_middle_tac "xaa = y" 1),
     (hyp_subst_tac 2),
     ((dtac (spec RS iffD2) 1) THEN (etac LFreeIn_LLamI 1)),
     (REPEAT (atac 1)),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LFreeIn_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
     ((dtac (spec RS iffD1) 1) THEN (atac 1)),
     (rtac LFreeIn_LsubstI1 1),
     (REPEAT (atac 1)),
     ((dtac (spec RS spec RS iffD2) 1) THEN 
    (rtac (exI RS exI) 1) THEN (etac LBoundBy_LLamI1 1)),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LBoundBy_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
     (res_inst_tac [("P", "%x. LFreeIn(<x, ?y>, ?X)")]
    (app_right_Nil RS subst) 1),
     (rtac LFreeIn_LsubstI2 2),
     ((dtac (spec RS iffD1) 4) THEN (atac 4)),
     (etac LFreeInE2 1),
     (etac LOcc_typeD1 1),
     (REPEAT (ares_tac ([LFO_I] @ LFreeIn_LTermIs) 1)),
    (* 45 *)
     (rtac LFreeInE 1),
     (atac 1),
     (hyp_subst_tac 1),
     (etac LFreeIn_LsubstE 1),
     (REPEAT (ares_tac LTerm.intrs 1)),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LFreeIn_LTermEs addSEs [LFO_E]
                           addSEs LTermOcc.Tag.free_SEs)) 2),
     ((dtac (spec RS iffD2) 1) THEN (atac 1)),
     ((dtac (spec RS iffD1) 1) THEN (etac LFreeIn_LLamI 1)),
     (fast_tac ZF_cs 1),
     (atac 1),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LFreeIn_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
     (subgoals_tac ["n: list(nat)"] 1),
     ((etac LFreeInE2 2) THEN (etac LOcc_typeD1 2) THEN (atac 2)),
     (asm_simp_tac (IFOL_ss addsimps [app_right_Nil]) 1),
     ((dtac (spec RS iffD2) 1) THEN (atac 1)),
     ((dtac (spec RS spec RS iffD1) 1) THEN (rtac (exI RS exI) 1) THEN
    (etac LBoundBy_LLamI1 1)),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LBoundBy_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
    (* 62 *)
     (forward_tac [LBoundByD1] 1),
     (etac LBindingE 1),
     (forward_tac [LBoundByD1] 2),
     (etac LBindingE 2),
     (safe_tac ZF_cs),
     ((dtac (spec RS spec RS iffD2) 1) THEN (rtac (exI RS exI) 1) THEN
    (etac LBoundBy_LLamI2 1)),
     (atac 1),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LBoundBy_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
     ((dtac (spec RS spec RS iffD1) 1) THEN (etac (exI RS exI) 1)),
     (REPEAT (etac exE 1)),
     (forw_inst_tac [("M", "xa")] LBoundByD1 1),
     (etac LBindingE 1),
     (SELECT_GOAL (safe_tac ZF_cs) 1),
     (REPEAT (rtac exI 1)),
     (rtac LBoundBy_LsubstI1 1),
     (REPEAT (ares_tac LTerm.intrs 1)),
    (* 79 *)
     (SELECT_GOAL (safe_tac (ZF_cs addSEs [LBoundBy_LsubstE]
                           addSEs LBoundBy_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
     ((dtac (spec RS spec RS iffD2) 1) THEN (etac (exI RS exI) 1)),
     (REPEAT (etac exE 1)),
     (forw_inst_tac [("M", "M")] LBoundByD1 1),
     (etac LBindingE 1),
     (SELECT_GOAL (safe_tac ZF_cs) 1),
     ((dtac (spec RS spec RS iffD1) 1) THEN (rtac (exI RS exI) 1) THEN
    (etac LBoundBy_LLamI2 1)),
     (atac 1),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LBoundBy_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
     (etac (exI RS exI) 1),
    (* 89 *)
     (rtac LFreeInE 1),
     (atac 1),
     (hyp_subst_tac 1),
     (rtac LFreeInE 2),
     (atac 2),
     (hyp_subst_tac 2),
     (excluded_middle_tac "xa = x" 1),
     (hyp_subst_tac 2),
     ((dtac (spec RS iffD1) 1) THEN (etac LFreeIn_LLamI 1)),
     (REPEAT (atac 1)),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LFreeIn_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
     ((dtac (spec RS spec RS iffD1) 1) THEN 
    (rtac (exI RS exI) 1) THEN (etac LBoundBy_LLamI1 1)),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LBoundBy_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
    (* 102 *)
     (excluded_middle_tac "xa = x" 1),
     (hyp_subst_tac 2),
     ((dtac (spec RS iffD2) 1) THEN (etac LFreeIn_LLamI 1)),
     (REPEAT (atac 1)),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LFreeIn_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
     ((dtac (spec RS spec RS iffD2) 1) THEN 
    (rtac (exI RS exI) 1) THEN (etac LBoundBy_LLamI1 1)),
     (SELECT_GOAL (safe_tac (ZF_cs addSEs LBoundBy_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)) 1),
    (* 109 *)
     (forward_tac [LBoundByD1] 1),
     (etac LBindingE 1),
     (forward_tac [LBoundByD1] 2),
     (etac LBindingE 2),
     (safe_tac ZF_cs),
     ((dtac (spec RS spec RS iffD1) 1) THEN 
    (rtac (exI RS exI) 1) THEN (etac LBoundBy_LLamI2 1)),
     ((dtac (spec RS spec RS iffD2) 3) THEN 
    (rtac (exI RS exI) 3) THEN (etac LBoundBy_LLamI2 3)),
     (safe_tac (ZF_cs addSEs LBoundBy_LTermEs addSEs list.free_SEs
                           addSEs LTermOcc.Tag.free_SEs)),
     (REPEAT (ares_tac [exI] 1))]);

qed_goalw "LAlpha_LAppE" LAlpha.thy [LAlpha_def]
    "[| LAlpha(LApp(A, B), N); \
\       !! C D. [| N = LApp(C, D); LAlpha(A, C); LAlpha(B, D) |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (etac conjE 1)),
     (etac LSkeltonEq_LAppE 1),
     (subgoals_tac ["A: LTerm", "B: LTerm", "C: LTerm", "D: LTerm"] 1),
     (REPEAT (eresolve_tac [LSkeltonEqD1, LSkeltonEqD2] 2)),
     (rtac prem 1),
     (atac 1),
     (safe_tac ZF_cs),
     (TRYALL ((rtac LFreeInE) THEN' atac THEN' hyp_subst_tac)),
     (TRYALL ((forward_tac [LBoundByD1]) THEN' (etac LBindingE))),
     (safe_tac ZF_cs),
    (**)
     ((dtac (spec RS spec RS iffD2) 8) THEN (rtac (exI RS exI) 8) THEN
      (etac LBoundBy_LAppI2 8)),
     ((dtac (spec RS spec RS iffD1) 7) THEN (rtac (exI RS exI) 7) THEN
      (etac LBoundBy_LAppI2 7)),
     ((dtac (spec RS iffD2) 6) THEN (etac LFreeIn_LAppI2 6)),
     ((dtac (spec RS iffD1) 5) THEN (etac LFreeIn_LAppI2 5)),
     ((dtac (spec RS spec RS iffD2) 4) THEN (rtac (exI RS exI) 4) THEN
      (etac LBoundBy_LAppI1 4)),
     ((dtac (spec RS spec RS iffD1) 3) THEN (rtac (exI RS exI) 3) THEN
      (etac LBoundBy_LAppI1 3)),
     ((dtac (spec RS iffD2) 2) THEN (etac LFreeIn_LAppI1 2)),
     ((dtac (spec RS iffD1) 1) THEN (etac LFreeIn_LAppI1 1)),
     (safe_tac (ZF_cs addSEs LFreeIn_LTermEs addSEs LBoundBy_LTermEs
                addSEs LTermOcc.Tag.free_SEs addSEs list.free_SEs)),
     (REPEAT (ares_tac [exI] 1))]);

val LAlpha_LTermEs = [LAlpha_LVarE, LAlpha_LLamE, LAlpha_LAppE];

(** Rules for depth induction **)
qed_goal "depth_ind_LLam" LAlpha.thy
    "[| LOcc(LLam(x, M)) <= Occ_fbs_op(LTag, Z); x: LVariable; M: LTerm |] \
\      ==> LOcc(M) <= domain(Z) * LTag"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (res_inst_tac [("P", "%x. x <= ?X")] ssubst 1),
     (eres_inst_tac [("b", "0")] Occ_subtree_Occ_fbs_op_lemma 2),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps 
                       ([LTermOcc.use_thm Occ_Term_cons, 
                         Occ_subtree_Occ_cons])) 1)]);

qed_goal "depth_ind_LApp1" LAlpha.thy
    "[| LOcc(LApp(M, N)) <= Occ_fbs_op(LTag, Z); M: LTerm; N: LTerm |] \
\      ==> LOcc(M) <= domain(Z) * LTag"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (res_inst_tac [("P", "%x. x <= ?X")] ssubst 1),
     (eres_inst_tac [("b", "0")] Occ_subtree_Occ_fbs_op_lemma 2),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps 
                       ([LTermOcc.use_thm Occ_Term_cons, 
                         Occ_subtree_Occ_cons])) 1)]);

qed_goal "depth_ind_LApp2" LAlpha.thy
    "[| LOcc(LApp(M, N)) <= Occ_fbs_op(LTag, Z); M: LTerm; N: LTerm |] \
\      ==> LOcc(N) <= domain(Z) * LTag"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (res_inst_tac [("P", "%x. x <= ?X")] ssubst 1),
     (eres_inst_tac [("b", "1")] Occ_subtree_Occ_fbs_op_lemma 2),
     (asm_simp_tac (LTermOcc.Term_cons_ss addsimps 
                       ([LTermOcc.use_thm Occ_Term_cons, 
                         Occ_subtree_Occ_cons])) 1)]);

qed_goalw "depth_ind_LSkeltonEq" LAlpha.thy [LSkeltonEq_def]
    "[| LSkeltonEq(M, N); LOcc(M) <= domain(Z) * LTag |] ==> \
\       LOcc(N) <= domain(Z) * LTag"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (safe_tac ZF_cs),
     (rtac (LOcc_domain RS subsetD RS SigmaE) 1),
     (atac 2),
     (safe_tac ZF_cs),
     (etac LTermOcc.Tag.elim 1),
     (ALLGOALS hyp_subst_tac),
     (ALLGOALS ((dtac (spec RS iffD2)) THEN' (atac ORELSE' (etac exI)))),
     (TRYALL (etac exE)),
     (ALLGOALS ((dtac subsetD) THEN' atac THEN' (etac SigmaD1)))]);

qed_goal "LAlpha_LsubstI" LAlpha.thy
    "[| LAlpha(M, M'); LAlpha(N, N'); \
\      LFreeForIn(N, x, M); LFreeForIn(N', x, M') \
\    |] ==> LAlpha(Lsubst(M, x, N), Lsubst(M', x, N'))"
  (fn prem1::prem2::prems =>
    [(cut_facts_tac ([prem1, prem2] RL [LAlphaD1] RL 
                   [LSkeltonEqD1, LSkeltonEqD2]) 1),
     (cut_facts_tac prems 1),
     (rtac LAlphaI 1),
     (rewrite_goals_tac [LSkeltonEq_def]),
     (safe_tac (ZF_cs addSEs [LOcc_LsubstE, LFO_E2] addSIs [Lsubst_type])),
     (TRYALL (dresolve_tac
            ([prem1, prem1 RS LAlpha_sym] RL [LAlphaD2]))),
     (TRYALL (forward_tac ([prem1, prem2, prem1 RS LAlpha_sym,
                           prem2 RS LAlpha_sym] RL [LAlphaD1] RL 
                          [LSkeltonEq_TLVarD, LSkeltonEq_TLLamD, 
                           LSkeltonEq_TLAppD]))),
     (TRYALL (etac exE)),
     (TRYALL (eresolve_tac ([LFO_I RS LOcc_LsubstI2] RL [exI, asm_rl]))),
     (TRYALL atac),
     (TRYALL (resolve_tac ([LOcc_LsubstI1] RL [exI, asm_rl]))),
     (TRYALL atac),
     (safe_tac (ZF_cs addSEs [LFO_E] addSEs LTermOcc.Tag.free_SEs)),
     (TRYALL (dresolve_tac
            ([prem1, prem1 RS LAlpha_sym] RL [LAlphaD2]))),
     (subgoals_tac ["TLVar(xa) = TLVar(x)"] 2),
     (etac LFreeInE2 3),
     (rtac (LOcc_in_Occ_range RS Occ_range_functionalD
          RS functionalD) 3),
     (atac 4),
     (REPEAT (atac 3)),
     (subgoals_tac ["TLVar(xa) = TLVar(x)"] 1),
     (etac LFreeInE2 2),
     (rtac (LOcc_in_Occ_range RS Occ_range_functionalD
          RS functionalD) 2),
     (atac 3),
     (REPEAT (atac 2)),
     (REPEAT ((etac notE 1) THEN (asm_simp_tac IFOL_ss 1) 
              THEN (etac LFO_I 1))),
     (safe_tac (ZF_cs addSEs [LFreeIn_LsubstE, LBoundBy_LsubstE, LFO_E2])),
     (TRYALL (dresolve_tac
            ([prem1, prem2, prem1 RS LAlpha_sym, prem2 RS LAlpha_sym] 
             RL [LAlphaD3]))),
     (REPEAT (fast_tac (ZF_cs addIs ([prem1, prem2, prem1 RS LAlpha_sym, 
                                      prem2 RS LAlpha_sym] RL [LAlphaD2])
                        addIs [LFO_I, LFreeIn_LsubstI2, LFreeIn_LsubstI1]
                        addIs [LBoundBy_LsubstI2, LBoundBy_LsubstI1]) 1))]);

