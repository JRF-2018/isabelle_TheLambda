(*
    File:        dAlpha.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open dAlpha;

(** dSkeltonEq **)
qed_goalw "dSkeltonEqD1" dAlpha.thy [dSkeltonEq_def]
    "dSkeltonEq(M, N) ==> M: dTerm"
  (fn [prem] =>
    [(rtac (prem RS conjunct1) 1)]);

qed_goalw "dSkeltonEqD2" dAlpha.thy [dSkeltonEq_def]
    "dSkeltonEq(M, N) ==> N: dTerm"
  (fn [prem] =>
    [(rtac (prem RS conjunct2 RS conjunct1) 1)]);

qed_goalw "dSkeltonEq_TdVarD" dAlpha.thy [dSkeltonEq_def]
    "[| dSkeltonEq(M, N); <l, TdVar(x)>: dOcc(M) |] \
\       ==> EX x. <l, TdVar(x)>: dOcc(N)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS conjunct2 RS conjunct1
          RS spec RS iffD1) 1),
     (rtac exI 1),
     (rtac prem 1)]);

qed_goalw "dSkeltonEq_TdBoundD" dAlpha.thy [dSkeltonEq_def]
    "[| dSkeltonEq(M, N); <l, TdBound(n)>: dOcc(M) |] \
\       ==> EX n. <l, TdBound(n)>: dOcc(N)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS conjunct2 RS conjunct2 RS conjunct1
          RS spec RS iffD1) 1),
     (rtac exI 1),
     (rtac prem 1)]);

qed_goalw "dSkeltonEq_TdLamD" dAlpha.thy [dSkeltonEq_def]
    "[| dSkeltonEq(M, N); <l, TdLam>: dOcc(M) |] \
\       ==> <l, TdLam>: dOcc(N)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS conjunct2 RS conjunct2 RS
            conjunct2 RS conjunct1 RS spec RS iffD1) 1),
     (rtac prem 1)]);

qed_goalw "dSkeltonEq_TdAppD" dAlpha.thy [dSkeltonEq_def]
    "[| dSkeltonEq(M, N); <l, TdApp>: dOcc(M) |] \
\       ==> <l, TdApp>: dOcc(N)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS conjunct2 RS conjunct2 
            RS conjunct2 RS conjunct2 RS spec RS iffD1) 1),
     (rtac prem 1)]);

qed_goalw "dSkeltonEq_refl" dAlpha.thy [dSkeltonEq_def]
    "M: dTerm ==> dSkeltonEq(M, M)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (fast_tac ZF_cs 1)]);

qed_goalw "dSkeltonEq_sym" dAlpha.thy [dSkeltonEq_def]
    "dSkeltonEq(M, N) ==> dSkeltonEq(N, M)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT ((etac (spec RS iff_sym) 1) ORELSE
            (ares_tac [conjI, allI] 1)))]);

qed_goalw "dSkeltonEq_trans" dAlpha.thy [dSkeltonEq_def]
    "[| dSkeltonEq(M, N); dSkeltonEq(N, L) |] ==> dSkeltonEq(M, L)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT (((etac (spec RS iff_trans) 1) THEN (etac spec 1)) ORELSE
            (ares_tac [conjI, allI] 1)))]);

qed_goalw "dSkeltonEq_dVarI" dAlpha.thy [dSkeltonEq_def]
    "[| x: LVariable; y: LVariable |] ==> dSkeltonEq(dVar(x), dVar(y))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (ares_tac (dTerm.intrs @ [conjI]) 1)),
     (rtac conjI 2),
     (ALLGOALS (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs
                        addSEs dOcc_dTermEs addIs dOcc_dTermIs
                        addIs [iffI])))]);

qed_goalw "dSkeltonEq_dBoundI" dAlpha.thy [dSkeltonEq_def]
    "[| n: nat; m: nat |] ==> dSkeltonEq(dBound(n), dBound(m))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (ares_tac (dTerm.intrs @ [conjI]) 1)),
     (rtac conjI 2),
     (ALLGOALS (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs
                        addSEs dOcc_dTermEs addIs dOcc_dTermIs
                        addIs [iffI])))]);

qed_goalw "dSkeltonEq_dLamI" dAlpha.thy [dSkeltonEq_def]
    "dSkeltonEq(M, N) ==> dSkeltonEq(dLam(M), dLam(N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT (ares_tac (dTerm.intrs @ [conjI]) 1)),
     (rtac conjI 2),
     (rtac conjI 3),
     (ALLGOALS (rtac (iffI RS allI))),
     (safe_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs
              addSEs dOcc_dTermEs)),
     (TRYALL (((dtac (spec RS iffD1)) THEN'(etac exI)) ORELSE'
            ((dtac (spec RS iffD2)) THEN'(etac exI)))),
     (TRYALL (((dtac (spec RS iffD1)) THEN'(atac)) ORELSE'
            ((dtac (spec RS iffD2)) THEN'(atac)))),
     (TRYALL (etac exE)),
     (REPEAT (ares_tac ([exI] @ dOcc_dTermIs) 1))]);

qed_goalw "dSkeltonEq_dAppI" dAlpha.thy [dSkeltonEq_def]
    "[| dSkeltonEq(A, C); dSkeltonEq(B, D)|] \
\       ==> dSkeltonEq(dApp(A, B), dApp(C, D))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT (ares_tac (dTerm.intrs @ [conjI]) 1)),
     (safe_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs
              addSEs dOcc_dTermEs)),
     (TRYALL (((dtac (spec RS iffD1)) THEN'(etac exI)) ORELSE'
            ((dtac (spec RS iffD2)) THEN'(etac exI)))),
     (TRYALL (((dtac (spec RS iffD1)) THEN'(atac)) ORELSE'
            ((dtac (spec RS iffD2)) THEN'(atac)))),
     (TRYALL (etac exE)),
     (REPEAT (ares_tac ([exI] @ dOcc_dTermIs) 1))]);

val dSkeltonEq_LTermIs = [dSkeltonEq_dVarI, dSkeltonEq_dBoundI,
                          dSkeltonEq_dLamI, dSkeltonEq_dAppI];

qed_goalw "dSkeltonEq_dVarE" dAlpha.thy [dSkeltonEq_def]
    "[| dSkeltonEq(dVar(x), N); \
\       !! y B. [| N = dVar(y); x: LVariable; y: LVariable |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac (dTerm_typeEs @ [conjE]) 1)),
     (subgoals_tac ["EX y: LVariable.  N = dVar(y)"] 1),
     (subgoals_tac ["EX y. <[], TdVar(y)>: dOcc(N)"] 2),
     (etac (spec RS iffD1) 3),
     (REPEAT (ares_tac ([exI] @ dOcc_dTermIs) 3)),
     (etac exE 2),
     (eres_inst_tac [("a", "N")] dTerm.elim 2),
     (TRYALL hyp_subst_tac),
     (REPEAT (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs
                        addSEs list.free_SEs
                        addSEs dOcc_dTermEs) 3)),
     (REPEAT (ares_tac [bexI, refl] 2)),
     (etac bexE 1),
     (rtac prem 1),
     (REPEAT (atac 1))]);

qed_goalw "dSkeltonEq_dBoundE" dAlpha.thy [dSkeltonEq_def]
    "[| dSkeltonEq(dBound(n), N); \
\       !! m B. [| N = dBound(m); n: nat; m: nat |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac (dTerm_typeEs @ [conjE]) 1)),
     (subgoals_tac ["EX m: nat.  N = dBound(m)"] 1),
     (subgoals_tac ["EX m. <[], TdBound(m)>: dOcc(N)"] 2),
     (etac (spec RS iffD1) 3),
     (REPEAT (ares_tac ([exI] @ dOcc_dTermIs) 3)),
     (etac exE 2),
     (eres_inst_tac [("a", "N")] dTerm.elim 2),
     (TRYALL hyp_subst_tac),
     (rtac bexI 3),
     (REPEAT (ares_tac [refl] 3)),
     (REPEAT (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs
                        addSEs list.free_SEs
                        addSEs dOcc_dTermEs) 2)),
     (etac bexE 1),
     (rtac prem 1),
     (REPEAT (atac 1))]);

qed_goalw "dSkeltonEq_dLamE" dAlpha.thy [dSkeltonEq_def]
    "[| dSkeltonEq(dLam(A), N); \
\       !! y B. [| N = dLam(B); dSkeltonEq(A, B) |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac (dTerm_typeEs @ [conjE]) 1)),
     (subgoals_tac ["EX B: dTerm. N = dLam(B)"] 1),
     (subgoals_tac ["<[], TdLam>: dOcc(N)"] 2),
     (etac (spec RS iffD1) 3),
     (REPEAT (ares_tac ([exI] @ dOcc_dTermIs) 3)),
     (eres_inst_tac [("a", "N")] dTerm.elim 2),
     (TRYALL hyp_subst_tac),
     (rtac bexI 4),
     (REPEAT (ares_tac [refl] 4)),
     (REPEAT (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs
              addSEs list.free_SEs
              addSEs dOcc_dTermEs) 2)),
     (etac bexE 1),
     (rtac prem 1),
     (REPEAT (ares_tac [conjI] 1)),
     (safe_tac ZF_cs),
     (TRYALL ((dtac (spec RS iffD1)) THEN' (eresolve_tac dOcc_dTermIs))),
     (TRYALL ((dtac (spec RS iffD2)) THEN' (eresolve_tac dOcc_dTermIs))),
     (TRYALL ((dtac (spec RS iffD1)) THEN' 
            (eresolve_tac (dOcc_dTermIs RL [exI])))),
     (TRYALL ((dtac (spec RS iffD1)) THEN' 
            (eresolve_tac (dOcc_dTermIs RL [exI])))),
     (TRYALL ((dtac (spec RS iffD2)) THEN' 
            (eresolve_tac (dOcc_dTermIs RL [exI])))),
     (safe_tac (ZF_cs addSEs list.free_SEs
              addSEs dOcc_dTermEs
              addSEs dTermOcc.Tag.free_SEs)),
     (ALLGOALS (etac exI))]);

qed_goalw "dSkeltonEq_dAppE" dAlpha.thy [dSkeltonEq_def]
    "[| dSkeltonEq(dApp(A, B), N); \
\       !! C D. [| N = dApp(C, D); dSkeltonEq(A, C); dSkeltonEq(B, D) |] \
\             ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac (dTerm_typeEs @ [conjE]) 1)),
     (subgoals_tac ["EX C: dTerm.  EX D: dTerm. N = dApp(C, D)"] 1),
     (subgoals_tac ["<[], TdApp>: dOcc(N)"] 2),
     (etac (spec RS iffD1) 3),
     (REPEAT (ares_tac dOcc_dTermIs 3)),
     (eres_inst_tac [("a", "N")] dTerm.elim 2),
     (rtac (bexI RS bexI) 5),
     (REPEAT (ares_tac [refl] 5)),
     (REPEAT (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs
                        addSEs list.free_SEs
                        addSEs dOcc_dTermEs) 2)),
     (REPEAT (etac bexE 1)),
     (rtac prem 1),
     (atac 1),
     (ALLGOALS hyp_subst_tac),
     (safe_tac ZF_cs),
     (TRYALL ((dtac (spec RS iffD1)) THEN' (eresolve_tac dOcc_dTermIs))),
     (TRYALL ((dtac (spec RS iffD2)) THEN' (eresolve_tac dOcc_dTermIs))),
     (TRYALL ((dtac (spec RS iffD1)) THEN' 
            (eresolve_tac (dOcc_dTermIs RL [exI])))),
     (TRYALL ((dtac (spec RS iffD2)) THEN' 
            (eresolve_tac (dOcc_dTermIs RL [exI])))),
     (safe_tac (ZF_cs addSEs list.free_SEs
              addSEs dOcc_dTermEs
              addSEs dTermOcc.Tag.free_SEs)),
     (ALLGOALS (etac exI))]);

val dSkeltonEq_dTermEs = [dSkeltonEq_dVarE, dSkeltonEq_dBoundE,
                          dSkeltonEq_dLamE, dSkeltonEq_dAppE];

qed_goal "dSkeltonEq_skelton" dAlpha.thy
    "[| dSkeltonEq(M, N); <l, T>: dOcc(M) |] ==> EX U. <l, U>: dOcc(N)"
  (fn [major, prem] =>
    [(cut_facts_tac [[prem, major RS dSkeltonEqD1] MRS dOcc_typeD2, prem] 1),
     (etac dTermOcc.Tag.elim 1),
     (TRYALL hyp_subst_tac),
     (ALLGOALS (dresolve_tac ([major] RL [dSkeltonEq_TdVarD, 
                                        dSkeltonEq_TdBoundD,
                                        dSkeltonEq_TdLamD, 
                                        dSkeltonEq_TdAppD]))),
     (TRYALL (etac exE)),
     (REPEAT (ares_tac [exI] 1))]);

qed_goal "dSkeltonEq_dLamDeg_lemma" dAlpha.thy
    "[| dSkeltonEq(M, N); <l, T>: dOcc(M); <l @ x, U>: dOcc(M) |] ==> \
\      dLamDeg(x, dsubterm(M, l)) = dLamDeg(x, dsubterm(N, l))"
  (fn [major, prem1, prem2] =>
    [(rtac (prem2 RS rev_mp) 1),
     (rtac (prem1 RS rev_mp) 1),
     (rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "N")] spec 1),
     (res_inst_tac [("x", "T")] spec 1),
     (res_inst_tac [("x", "l"), ("A", "list(nat)")] bspec 1),
     (res_inst_tac [("x", "x"), ("A", "list(nat)")] bspec 1),
     (rtac ([prem2, major RS dSkeltonEqD1] MRS dOcc_typeD1 RS app_typeD) 2),
     (REPEAT (rtac ([prem1, major RS dSkeltonEqD1] MRS dOcc_typeD1) 2)),
     (dTermOcc.ind_tac "M" [major RS dSkeltonEqD1] 1),
     (safe_tac (ZF_cs addSEs dSkeltonEq_dTermEs addSEs [ConsE]
              addSEs dOcc_dTermEs addSEs dTermOcc.Tag.free_SEs)),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss addsimps 
                                 (dTerm.intrs @ [dSkeltonEqD1, 
                                                 dSkeltonEqD2,
                                                 dOcc_typeD1])))),
     (safe_tac (ZF_cs addSEs list.free_SEs addSEs [ConsE])),
     (TRYALL (etac (bspec RS bspec RS spec RS spec RS mp RS mp RS mp))),
     (TRYALL (REPEAT o (ares_tac [dOcc_typeD1]))),
     (forw_inst_tac [("M", "M")] 
    (dTermOcc.use_thm Occ_ind_cond_Occ_not_empty_lemma) 1),
     (forw_inst_tac [("M", "M")] 
    (dTermOcc.use_thm Occ_ind_cond_Occ_not_empty_lemma) 2),
     (forw_inst_tac [("M", "N")] 
    (dTermOcc.use_thm Occ_ind_cond_Occ_not_empty_lemma) 3),
     (ALLGOALS (etac bexE)),
     (ALLGOALS (fn i=>
              (dres_inst_tac [("x", "l")] bspec i) THEN
              (dres_inst_tac [("x", "[]")] bspec (i + 1)) THEN
              (dtac (spec RS spec RS mp RS mp RS mp) (i + 2)) THEN
              (atac (i + 3)))),
     (TRYALL atac),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss addsimps 
                                 (dTerm.intrs @ [dSkeltonEqD1, 
                                                 dSkeltonEqD2,
                                                 dOcc_typeD1]))))]);

(** dAlpha **)
qed_goalw "dAlphaD1" dAlpha.thy [dAlpha_def]
    "dAlpha(M, N) ==> dSkeltonEq(M, N)"
  (fn [prem] =>
    [(rtac (prem RS conjunct1) 1)]);

qed_goalw "dAlphaD2" dAlpha.thy [dAlpha_def]
    "[| dAlpha(M, N); <l, TdVar(x)>: dOcc(M) |] ==> <l, TdVar(x)>: dOcc(N)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS conjunct1 RS spec RS spec RS iffD1) 1),
     (rtac prem 1)]);

qed_goalw "dAlphaD3" dAlpha.thy [dAlpha_def]
    "[| dAlpha(M, N); dBoundBy(<l, T>, <m, U>, M) |] \
\       ==> EX n. dBoundBy(<l, TdBound(n)>, <m, TdLam>, N)"
  (fn [major, prem] =>
    [(cut_facts_tac [major RS conjunct2 RS conjunct2] 1),
     (dtac (spec RS spec RS iffD1) 1),
     (rtac (exI RS exI) 1),
     (rtac prem 1),
     (REPEAT (etac exE 1)),
     (rtac dBoundByE 1),
     (atac 1),
     (fast_tac ZF_cs 1)]);

qed_goal "dAlpha_dBoundByD" dAlpha.thy
    "[| dAlpha(M, N); dBoundBy(<l, T>, <m, U>, M) |] \
\       ==> dBoundBy(<l, T>, <m, U>, N)"
  (fn [major, prem] =>
    [(rtac (prem RS dBoundByE) 1),
     (cut_facts_tac [[major, prem] MRS dAlphaD3] 1),
     (safe_tac (ZF_cs addSEs [dBoundByE] addSDs [app_right_inj]
                addSEs dTermOcc.Tag.free_SEs)),
     (etac dOcc_typeD1 1),
     (atac 1),
     ((forward_tac [major RS dAlphaD1 RS dSkeltonEq_dLamDeg_lemma] 1)
      THEN (atac 1)),
     (asm_full_simp_tac (IFOL_ss addsimps [succ_inject_iff]) 1),
     (hyp_subst_tac 1),
     (REPEAT (ares_tac [refl, dBoundByI] 1))]);

qed_goalw "dAlphaI" dAlpha.thy [dAlpha_def]
    "[| dSkeltonEq(M, N); \
\        !! l x. <l, TdVar(x)>: dOcc(M) <-> <l, TdVar(x)>: dOcc(N); \
\        !! l m. (EX x. dBoundBy(<l, TdBound(x)>, <m, TdLam>, M))\
\                <-> (EX x. dBoundBy(<l, TdBound(x)>, <m, TdLam>, N)) \
\    |] ==> dAlpha(M, N)"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem1 RS conjI) 1),
     (rtac (allI RS allI RS conjI) 1),
     (rtac prem2 1),
     (safe_tac ZF_cs),
     (ALLGOALS ((rtac dBoundByE) THEN' atac)),
     (safe_tac ZF_cs),
     (dtac (exI RS (prem3 RS iffD1)) 1),
     (dtac (exI RS (prem3 RS iffD2)) 2),
     (ALLGOALS (fast_tac ZF_cs))]);

qed_goal "dAlpha_dPropI" dAlpha.thy
    "[| M: dProp; N: dProp; \
\       !! l. <l, TdLam>: dOcc(M) <-> <l, TdLam>: dOcc(N); \
\       !! l. <l, TdApp>: dOcc(M) <-> <l, TdApp>: dOcc(N); \
\       !! l x. <l, TdVar(x)>: dOcc(M) <-> <l, TdVar(x)>: dOcc(N); \
\       !! l m. (EX x. dBoundBy(<l, TdBound(x)>, <m, TdLam>, M))\
\               <-> (EX x. dBoundBy(<l, TdBound(x)>, <m, TdLam>, N)) \
\    |] ==> dAlpha(M, N)"
  (fn [prem1, prem2, prem3, prem4, prem5, prem6] =>
    [(rtac dAlphaI 1),
     (REPEAT (ares_tac [prem5, prem6] 2)),
     (rewrite_goals_tac [dSkeltonEq_def]),
     (REPEAT (ares_tac [conjI, prem1, prem2, dPropD1] 1)),
     (rtac conjI 2),
     (rtac conjI 3),
     (ALLGOALS (rtac allI)),
     (REPEAT (ares_tac [prem3, prem4] 3)),
     (safe_tac ZF_cs),
     ((dtac (prem5 RS iffD1) 1) THEN (etac exI 1)),
     ((dtac (prem5 RS iffD2) 1) THEN (etac exI 1)),
     (dtac (prem1 RS dProp_dBoundBy_lemma1) 1),
     (dtac (prem2 RS dProp_dBoundBy_lemma1) 2),
     (ALLGOALS (etac exE)),
     (dtac (exI RS (prem6 RS iffD1)) 1),
     (dtac (exI RS (prem6 RS iffD2)) 2),
     (REPEAT (fast_tac (ZF_cs addSEs [dBoundByE]) 1))]);

qed_goalw "dAlpha_refl" dAlpha.thy [dAlpha_def]
    "M: dTerm ==> dAlpha(M, M)"
  (fn [major] =>
    [(cut_facts_tac [major] 1),
     (fast_tac (ZF_cs addIs [dSkeltonEq_refl]) 1)]);

qed_goalw "dAlpha_sym" dAlpha.thy [dAlpha_def]
    "dAlpha(M, N) ==> dAlpha(N, M)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT ((etac dSkeltonEq_sym 1) ORELSE
              (etac (spec RS iff_sym) 1) ORELSE
              (etac (spec RS spec RS iff_sym) 1) ORELSE
              (ares_tac [conjI, allI] 1)))]);

qed_goalw "dAlpha_trans" dAlpha.thy [dAlpha_def]
    "[| dAlpha(M, N); dAlpha(N, L) |] ==> dAlpha(M, L)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac conjE 1)),
     (REPEAT (((etac dSkeltonEq_trans 1) THEN (atac 1)) ORELSE
              ((etac (spec RS iff_trans) 1) THEN (etac spec 1)) ORELSE
              ((etac (spec RS spec RS iff_trans) 1) THEN 
               (etac (spec RS spec) 1)) ORELSE
              (ares_tac [conjI, allI] 1)))]);

qed_goal "dAlpha_imp_dProp_eq" dAlpha.thy
    "[| dAlpha(M, N); M: dProp; N: dProp |] ==> M = N"
  (fn [major, prem1, prem2] =>
    [(cut_facts_tac ([prem1, prem2] RL [dPropD1]) 1),
     (rtac (dTermOcc.use_thm Occ_ind_cond_Occ_inj RS iffD1) 1),
     (REPEAT (ares_tac [equalityI] 1)),
     (ALLGOALS (rtac subsetI)),
     (ALLGOALS ((rtac (dOcc_domain RS subsetD RS SigmaE)) THEN' 
              (fn i=> atac (i + 1)))),
     (TRYALL atac),
     (ALLGOALS (etac dTermOcc.Tag.elim)),
     (ALLGOALS (REPEAT o hyp_subst_tac)),
     (dtac (prem2 RS dProp_dBoundBy_lemma1) 6),
     (dtac (prem1 RS dProp_dBoundBy_lemma1) 2),
     (etac exE 6),
     (etac exE 2),
     (dtac (major RS dAlpha_sym RS dAlpha_dBoundByD) 6),
     (dtac (major RS dAlpha_dBoundByD) 2),
     (safe_tac (ZF_cs addSEs [dBoundByE] addSEs dTermOcc.Tag.free_SEs)),
     (ALLGOALS (eresolve_tac 
              ([major, major RS dAlpha_sym] RL
               [dAlphaD2, dAlphaD1 RS dSkeltonEq_TdLamD,
                dAlphaD1 RS dSkeltonEq_TdAppD])))]);

qed_goal "dAlpha_dProp_iff" dAlpha.thy
    "[| M: dProp; N: dProp |] ==> dAlpha(M, N) <-> M = N"
  (fn [prem1, prem2] =>
    [(rtac iffI 1),
     (hyp_subst_tac 2),
     (rtac (prem2 RS dPropD1 RS dAlpha_refl) 2),
     (etac dAlpha_imp_dProp_eq 1),
     (REPEAT (ares_tac [prem1, prem2] 1))]);

(** Rules for depth induction **)
qed_goal "depth_ind_dLam" dAlpha.thy
    "[| dOcc(dLam(M)) <= Occ_fbs_op(dTag, Z); M: dTerm |] \
\      ==> dOcc(M) <= domain(Z) * dTag"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (res_inst_tac [("P", "%x. x <= ?X")] ssubst 1),
     (eres_inst_tac [("b", "0")] Occ_subtree_Occ_fbs_op_lemma 2),
     (asm_simp_tac (dTermOcc.Term_cons_ss addsimps 
                       ([dTermOcc.use_thm Occ_Term_cons, 
                         Occ_subtree_Occ_cons])) 1)]);

qed_goal "depth_ind_dApp1" dAlpha.thy
    "[| dOcc(dApp(M, N)) <= Occ_fbs_op(dTag, Z); M: dTerm; N: dTerm |] \
\      ==> dOcc(M) <= domain(Z) * dTag"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (res_inst_tac [("P", "%x. x <= ?X")] ssubst 1),
     (eres_inst_tac [("b", "0")] Occ_subtree_Occ_fbs_op_lemma 2),
     (asm_simp_tac (dTermOcc.Term_cons_ss addsimps 
                       ([dTermOcc.use_thm Occ_Term_cons, 
                         Occ_subtree_Occ_cons])) 1)]);

qed_goal "depth_ind_dApp2" dAlpha.thy
    "[| dOcc(dApp(M, N)) <= Occ_fbs_op(dTag, Z); M: dTerm; N: dTerm |] \
\      ==> dOcc(N) <= domain(Z) * dTag"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (res_inst_tac [("P", "%x. x <= ?X")] ssubst 1),
     (eres_inst_tac [("b", "1")] Occ_subtree_Occ_fbs_op_lemma 2),
     (asm_simp_tac (dTermOcc.Term_cons_ss addsimps 
                       ([dTermOcc.use_thm Occ_Term_cons, 
                         Occ_subtree_Occ_cons])) 1)]);

qed_goal "depth_ind_dSubst_dVar_lemma" dAlpha.thy
    "[| <l, T>: dOcc(dSubst(M, n, dVar(x))); \
\       M: dTerm; x: LVariable; n: nat \
\    |] ==> EX T. <l, T>: dOcc(M)"
  (fn [major, prem1, prem2, prem3] =>
    [(cut_facts_tac [prem2] 1),
     (rtac (major RS rev_mp) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (res_inst_tac [("x", "l")] spec 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (rtac (ballI RS allI) 2),
     (excluded_middle_tac "xaa = n" 2),
     (excluded_middle_tac "xaa < n" 2),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs)),
     (TRYALL ((etac (spec RS bspec RS mp RS exE)) THEN' 
            atac THEN' atac)),
     (((etac (spec RS bspec RS mp RS exE)) THEN' (etac nat_succI) 
     THEN' atac) 6),
     (ALLGOALS (rtac exI)),
     (ALLGOALS (resolve_tac dOcc_dTermIs)),
     (REPEAT (atac 1))]);

qed_goalw "depth_ind_dSubst_dVar" dAlpha.thy [Occ_fbs_op_def]
    "[| dOcc(M) <= domain(Z) * dTag; M: dTerm; x: LVariable; n: nat |] ==> \
\       dOcc(dSubst(M, n, dVar(x))) <= domain(Z) * dTag"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac subsetI 1),
     (rtac (dOcc_domain RS subsetD RS SigmaE) 1),
     (atac 2),
     (REPEAT (ares_tac ([dSubst_type, prem1, prem2, prem3] @ dTerm.intrs) 1)),
     (hyp_subst_tac 1),
     (forward_tac [depth_ind_dSubst_dVar_lemma] 1),
     (etac exE 4),
     (rtac SigmaI 4),
     (etac (major RS subsetD RS SigmaD1) 4),
     (REPEAT (ares_tac [prem2, prem3, prem1] 1))]);
