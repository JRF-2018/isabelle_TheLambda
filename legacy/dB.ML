(*
    File:        dB.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open dB;

val dB_eqns = map (fn s => prove_goalw dB.thy [dB_def] s
                   (fn prems =>
                    [(cut_facts_tac prems 1),
                     (asm_simp_tac (IFOL_ss addsimps LTermOcc.rec_eqns) 1)]))
    ["dB(LVar(x)) = dVar(x)",
     "dB(LLam(x, M)) = dLam(dAbst(dB(M), x, 0))",
     "dB(LApp(A, B)) = dApp(dB(A), dB(B))"];

qed_goal "dB_type" dB.thy
    "M: LTerm ==> dB(M): dProp"
  (fn [prem] =>
    [(LTermOcc.ind_tac "M" [prem] 1),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps dB_eqns))),
     (excluded_middle_tac "x : dFV(dB(M))" 2),
     (etac dPropE 3),
     (rtac dProp_dLamI2 3),
     (asm_simp_tac (dTerm_ss addsimps [dDeg_dAbst_lemma2]) 4),
     (forward_tac [dPropD1] 2),
     (asm_simp_tac (dTerm_ss addsimps [dDeg_dAbst_lemma1]) 2),
     (etac dProp_dLamI1 2),
     (REPEAT (ares_tac (dProp_dTermIs @ [dAbst_type, nat_0I]) 1))]);

qed_goal "LFreeIn_imp_dFreeIn" dB.thy
    "LFreeIn(<l, TLVar(x)>, M) ==> <l, TdVar(x)>: dOcc(dB(M))"
  (fn [prem] =>
    [(rtac (prem RS rev_mp) 1),
     (res_inst_tac [("x", "l")] spec 1),
     (LTermOcc.ind_tac "M" [prem RS LFreeInD1] 1),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps dB_eqns))),
     (safe_tac (ZF_cs addSEs LFreeIn_LTermEs
              addSEs LTermOcc.Tag.free_SEs)),
     (ALLGOALS (resolve_tac (dOcc_dTermIs))),
     (rtac dOcc_dAbstI2 1),
     (etac (dB_type RS dPropD1) 3),
     (rtac nat_0I 3),
     (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs) 2),
     (ALLGOALS (asm_simp_tac ZF_ss))]);

qed_goal "dFreeIn_imp_LFreeIn" dB.thy
    "[| <l, TdVar(x)>: dOcc(dB(M)); M: LTerm |] \
\       ==> LFreeIn(<l, TLVar(x)>, M)"
  (fn [prem1, prem2] =>
    [(rtac (prem1 RS rev_mp) 1),
     (res_inst_tac [("x", "l")] spec 1),
     (LTermOcc.ind_tac "M" [prem2] 1),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps dB_eqns))),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs
              addSEs dTermOcc.Tag.free_SEs)),
     (forward_tac [dOcc_dAbst_lemma1] 2),
     (etac dOcc_dAbstE 4),
     (REPEAT ((etac (dB_type RS dPropD1) 2) ORELSE (rtac nat_0I 2))),
     (ALLGOALS (resolve_tac LFreeIn_LTermIs)),
     (TRYALL atac),
     (safe_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs)),
     (ALLGOALS (asm_simp_tac ZF_ss))]);

qed_goal "dBoundBy_imp_LBoundBy" dB.thy
    "[| dBoundBy(<l, T>, <m, U>, dB(M)); M: LTerm |] \
\       ==> EX T U. LBoundBy(<l, T>, <m, U>, M)"
  (fn [prem1, prem2] =>
    [(rtac (prem1 RS rev_mp) 1),
     (res_inst_tac [("x", "m")] spec 1),
     (res_inst_tac [("x", "l")] spec 1),
     (LTermOcc.ind_tac "M" [prem2] 1),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps dB_eqns))),
     (safe_tac (ZF_cs addSEs dBoundBy_dTermEs
              addSEs dTermOcc.Tag.free_SEs)),
     (subgoal_tac "EX T. <m, T>: dOcc(dB(M))" 1),
     (etac dOcc_dAbstE 2),
     (rtac exI 5),
     (rtac exI 4),
     (REPEAT (ares_tac [dB_type RS dPropD1, nat_0I] 2)),
     (etac exE 1),
     (cut_inst_tac [("n", "0"), ("x", "x")] dLamDeg_dAbst_lemma 1),
     (etac (dB_type RS dPropD1) 1),
     (REPEAT (ares_tac [nat_0I] 1)),
     (rotate_tac 6 1),
     (asm_full_simp_tac IFOL_ss 1),
     (dtac (dOcc_dAbst_lemma3 RS dFreeIn_imp_LFreeIn) 1),
     (REPEAT (ares_tac [dB_type] 1)),
     (rtac (exI RS exI) 1),
     (etac LBoundBy_LLamI1 1),
     (dtac dBoundBy_dAbstD 1),
     (REPEAT (ares_tac [dB_type RS dPropD1, nat_0I] 1)),
     (ALLGOALS ((dtac (spec RS spec RS mp)) THEN' atac)),
     (ALLGOALS (REPEAT o (etac exE))),
     (ALLGOALS (rtac (exI RS exI))),
     (ALLGOALS (eresolve_tac LBoundBy_LTermIs)),
     (REPEAT (atac 1))]);


qed_goal "LBoundBy_imp_dBoundBy" dB.thy
    "LBoundBy(<l, T>, <m, U>, M) \
\            ==> EX T U. dBoundBy(<l, T>, <m, U>, dB(M))"
  (fn [prem1] =>
    [(rtac (prem1 RS rev_mp) 1),
     (res_inst_tac [("x", "m")] spec 1),
     (res_inst_tac [("x", "l")] spec 1),
     (LTermOcc.ind_tac "M" [prem1 RS LBoundByD1 RS LBindingD1] 1),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps dB_eqns))),
     (safe_tac (ZF_cs addSEs LBoundBy_LTermEs
              addSEs LTermOcc.Tag.free_SEs)),
     (dtac LFreeIn_imp_dFreeIn 1),
     (rtac (exI RS exI) 1),
     (rtac dBoundBy_dLamI1 1),
     (etac dOcc_dAbstI1 3),
     (asm_simp_tac arith_ss 2),
     (REPEAT (ares_tac [dAbst_type, dB_type RS dPropD1,
                      dLamDeg_dAbst_lemma, nat_0I] 1)),
     (ALLGOALS ((dtac (spec RS spec RS mp)) THEN' atac)),
     (ALLGOALS (REPEAT o (etac exE))),
     (ALLGOALS (rtac (exI RS exI))),
     (ALLGOALS (resolve_tac dBoundBy_dTermIs)),
     (REPEAT (ares_tac [dBoundBy_dAbstI, nat_0I, dB_type RS dPropD1] 1))]);

qed_goal "dOcc_TdLam_imp_LOcc_TLLam" dB.thy
    "[| <l, TdLam>: dOcc(dB(M)); M: LTerm |] ==> \
\        EX x. <l, TLLam(x)>: LOcc(M)"
  (fn [major, prem] =>
    [(rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "l")] spec 1),
     (LTermOcc.ind_tac "M" [prem] 1),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps dB_eqns))),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs [dOcc_dAbstE]
              addSEs dTermOcc.Tag.free_SEs)),
     (REPEAT (ares_tac [dB_type RS dPropD1, nat_0I] 2)),
     (TRYALL ((dtac (spec RS mp)) THEN' atac)),
     (TRYALL (etac exE)),
     (REPEAT (ares_tac ([exI] @ LOcc_LTermIs) 1))]);

qed_goal "LOcc_TLLam_imp_dOcc_TdLam" dB.thy
    "[| <l, TLLam(x)>: LOcc(M); M: LTerm |] ==> \
\        <l, TdLam>: dOcc(dB(M))"
  (fn [major, prem] =>
    [(rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "l")] spec 1),
     (LTermOcc.ind_tac "M" [prem] 1),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps dB_eqns))),
     (safe_tac (ZF_cs addSEs LOcc_LTermEs
              addSEs LTermOcc.Tag.free_SEs)),
     (TRYALL ((dtac (spec RS mp)) THEN' atac)),
     (resolve_tac dOcc_dTermIs 2),
     (etac dOcc_dAbstI2 2),
     (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs) 2),
     (REPEAT (ares_tac ([exI, dB_type RS dPropD1, 
                         nat_0I] @ dOcc_dTermIs) 1))]);

qed_goal "dOcc_TdApp_imp_LOcc_TLApp" dB.thy
    "[| <l, TdApp>: dOcc(dB(M)); M: LTerm |] ==> \
\        <l, TLApp>: LOcc(M)"
  (fn [major, prem] =>
    [(rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "l")] spec 1),
     (LTermOcc.ind_tac "M" [prem] 1),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps dB_eqns))),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs [dOcc_dAbstE]
              addSEs dTermOcc.Tag.free_SEs)),
     (REPEAT (ares_tac [dB_type RS dPropD1, nat_0I] 1)),
     (TRYALL ((dtac (spec RS mp)) THEN' atac)),
     (REPEAT (ares_tac ([exI] @ LOcc_LTermIs) 1))]);

qed_goal "LOcc_TLApp_imp_dOcc_TdApp" dB.thy
    "[| <l, TLApp>: LOcc(M); M: LTerm |] ==> \
\        <l, TdApp>: dOcc(dB(M))"
  (fn [major, prem] =>
    [(rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "l")] spec 1),
     (LTermOcc.ind_tac "M" [prem] 1),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps dB_eqns))),
     (safe_tac (ZF_cs addSEs LOcc_LTermEs
              addSEs LTermOcc.Tag.free_SEs)),
     (TRYALL ((dtac (spec RS mp)) THEN' atac)),
     (resolve_tac dOcc_dTermIs 1),
     (etac dOcc_dAbstI2 1),
     (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs) 1),
     (REPEAT (ares_tac ([exI, dB_type RS dPropD1, 
                         nat_0I] @ dOcc_dTermIs) 1))]);

qed_goal "LAlpha_imp_dAlpha" dB.thy
    "LAlpha(M, N) ==> dAlpha(dB(M), dB(N))"
  (fn [major] =>
    [(cut_facts_tac [major RS LAlphaD1 RS LSkeltonEqD1,
                   major RS LAlphaD1 RS LSkeltonEqD2] 1),
     (rtac dAlpha_dPropI 1),
     (REPEAT (ares_tac [dB_type] 1)),
     (safe_tac ZF_cs),
     (ALLGOALS (dresolve_tac [dOcc_TdLam_imp_LOcc_TLLam,
                          dOcc_TdApp_imp_LOcc_TLApp,
                          dFreeIn_imp_LFreeIn,
                          dBoundBy_imp_LBoundBy])),
     (TRYALL (atac ORELSE' (REPEAT o (etac exE)))),
     (ALLGOALS (dresolve_tac ([major, major RS LAlpha_sym] RL
                          [LAlphaD2, LAlphaD3,
                           LAlphaD1 RS LSkeltonEq_TLLamD,
                           LAlphaD1 RS LSkeltonEq_TLAppD]))),
     (TRYALL (atac ORELSE' (REPEAT o (etac exE)))),
     (ALLGOALS (dresolve_tac [LOcc_TLLam_imp_dOcc_TdLam,
                          LOcc_TLApp_imp_dOcc_TdApp,
                          LFreeIn_imp_dFreeIn,
                          LBoundBy_imp_dBoundBy])),
     (TRYALL (atac ORELSE' (REPEAT o (etac exE)))),
     (REPEAT (fast_tac (ZF_cs addSEs [dBoundByE] addIs [dBoundByI]) 1))]);

qed_goal "dAlpha_imp_LAlpha" dB.thy
    "[| dAlpha(dB(M), dB(N)); M: LTerm; N: LTerm |] ==> LAlpha(M, N)"
  (fn [major, prem1, prem2] =>
    [(cut_facts_tac [prem1, prem2] 1),
     (rtac LAlphaI2 1),
     (safe_tac ZF_cs),
     (ALLGOALS (dresolve_tac [LOcc_TLLam_imp_dOcc_TdLam,
                          LOcc_TLApp_imp_dOcc_TdApp,
                          LFreeIn_imp_dFreeIn,
                          LBoundBy_imp_dBoundBy])),
     (TRYALL (atac ORELSE' (REPEAT o (etac exE)))),
     (ALLGOALS (dresolve_tac ([major, major RS dAlpha_sym] RL
                          [dAlphaD2, dAlpha_dBoundByD,
                           dAlphaD1 RS dSkeltonEq_TdLamD,
                           dAlphaD1 RS dSkeltonEq_TdAppD]))),
     (TRYALL (atac ORELSE' (REPEAT o (etac exE)))),
     (ALLGOALS (dresolve_tac [dOcc_TdLam_imp_LOcc_TLLam,
                          dOcc_TdApp_imp_LOcc_TLApp,
                          dFreeIn_imp_LFreeIn,
                          dBoundBy_imp_LBoundBy])),
     (TRYALL (atac ORELSE' (REPEAT o (etac exE)))),
     (REPEAT (fast_tac (ZF_cs addSEs [LBoundByE] addIs [LBoundByI]) 1))]);

(** Now, we can prove correspondence between our alpha-equivarence, LAlpha,
    and equivarence under the de Bruijn notation, LAlpha3. **)

qed_goalw "LAlpha3_iff_LAlpha" dB.thy [LAlpha3_def]
    "LAlpha3(M, N) <-> LAlpha(M, N)"
  (fn _ =>
    [(rtac iffI 1),
     (REPEAT (etac conjE 1)),
     (rtac dAlpha_imp_LAlpha 1),
     (asm_simp_tac IFOL_ss 1),
     (rtac dAlpha_refl 1),
     (REPEAT (ares_tac [dB_type RS dPropD1] 1)),
     (forward_tac [LAlphaD1 RS LSkeltonEqD1] 1),
     (forward_tac [LAlphaD1 RS LSkeltonEqD2] 1),
     (dtac (LAlpha_imp_dAlpha RS dAlpha_imp_dProp_eq) 1),
     (REPEAT (ares_tac [dB_type, conjI] 1))]);

qed_goalw "LAlpha3D1" dB.thy [LAlpha3_def]
    "LAlpha3(M, N) ==> M: LTerm"
  (fn [major] =>
    [(rtac (major RS conjunct1) 1)]);

qed_goalw "LAlpha3D2" dB.thy [LAlpha3_def]
    "LAlpha3(M, N) ==> N: LTerm"
  (fn [major] =>
    [(rtac (major RS conjunct2 RS conjunct1) 1)]);

qed_goalw "LAlpha3D3" dB.thy [LAlpha3_def]
    "LAlpha3(M, N) ==> dB(M) = dB(N)"
  (fn [major] =>
    [(rtac (major RS conjunct2 RS conjunct2) 1)]);

val LAlpha_imp_dB_eq = standard 
    (LAlpha3_iff_LAlpha RS iffD2 RS LAlpha3D3);

qed_goal "dProp_LTerm_lemma" dB.thy
    "[| Infinite(LVariable); M: dProp |] ==> EX M': LTerm. M = dB(M')"
  (fn [infv, prem] =>
    [(rtac (prem RS rev_mp) 1),
     (rtac (prem RS dPropD1 RS 
          (dTermOcc.use_thm def_Terms_depth_induct)) 1),
     (etac dTerm.elim 1),
     (ALLGOALS hyp_subst_tac),
     (forward_tac [depth_ind_dApp1] 4),
     (forward_tac [depth_ind_dApp2] 6),
     (forward_tac [depth_ind_dLam] 3),
     (rtac ([infv, dFV_Fin] MRS InfiniteE) 4),
     (atac 4),
     (safe_tac (ZF_cs addSEs dProp_dTermEs)),
     (dres_inst_tac [("M", "Ma"), ("x", "x"), ("n", "0")] 
      depth_ind_dSubst_dVar 3),
     (forw_inst_tac [("M", "Ma"), ("N", "dVar(x)")] dDeg_dSubst_lemma3 6),
     (REPEAT (ares_tac [nat_0I, dProp_dVarI] 3)),
     (res_inst_tac [("x", "LVar(x)")] bexI 1),
     (asm_simp_tac (IFOL_ss addsimps dB_eqns) 1),
     (REPEAT (ares_tac LTerm.intrs 1)),
     (forw_inst_tac [("x", "Ma")] bspec 3),
     (dres_inst_tac [("x", "N")] bspec 4),
     (dres_inst_tac [("x", "dSubst(Ma, 0, dVar(x))")] bspec 2),
     (dres_inst_tac [("x", "Ma")] bspec 1),
     (TRYALL (REPEAT o (ares_tac ([dSubst_type, nat_0I] @ dTerm.intrs)))),
     (ALLGOALS (REPEAT o ((dtac (mp RS mp)) THEN' atac THEN' atac))),
     (ALLGOALS (REPEAT o (etac bexE))),
     (res_inst_tac [("x", "LApp(M', M'a)")] bexI 3),
     (res_inst_tac [("x", "LLam(x, M')")] bexI 2),
     (res_inst_tac [("x", "LLam(x, M')")] bexI 1),
     (TRYALL (REPEAT o (ares_tac LTerm.intrs))),
     (dtac sym 2),
     (dtac sym 2),
     (forward_tac [dDeg_dAbst_lemma1] 1),
     (REPEAT (ares_tac [nat_0I] 1)),
     (hyp_subst_tac 1),
     (ALLGOALS (asm_simp_tac (dTerm_ss addsimps dB_eqns
                            addsimps [dAbst_dSubst_lemma])))]);

(** LFV and dFV **)
qed_goal "LFV_eq_dFV_dB" dB.thy
    "M: LTerm ==> LFV(M) = dFV(dB(M))"
  (fn [major] =>
    [(LTermOcc.ind_tac "M" [major] 1),
     (ALLGOALS (asm_simp_tac (dTerm_ss addsimps dB_eqns
			    addsimps LFV_eqns
			    addsimps [dB_type RS dPropD1, dFV_dAbst,
				      dAbst_type])))]);

(** isSubst **)
qed_goal "dsubst_lemma1" dB.thy
    "[| x ~: dFV(M); dDeg(M) le n; \
\      M: dTerm; n: nat; N: dTerm \
\    |] ==> dSubst(dAbst(M, x, n), n, N) = M"
  (fn prems =>
    [(rtac (dDeg_dAbst_lemma1 RS ssubst) 1),
     (rtac dDeg_dSubst_lemma1 4),
     (REPEAT (ares_tac prems 1))]);

qed_goal "dsubst_lemma2" dB.thy
    "[| x ~: dFV(N); dDeg(M) le n; x ~= y; \
\      M: dTerm; n: nat; N: dTerm \
\    |] ==> \
\      dSubst(dAbst(dAbst(M, x, n), y, succ(n)), succ(n), N) \
\        = dAbst(dSubst(dAbst(M, y, n), n, N), x, n)"
  (fn [major, sub, prem0, prem1, prem2, prem3] =>
    [(cut_facts_tac [prem0] 1),
     (rtac (sub RS rev_mp) 1),
     (rtac (major RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (ALLGOALS (rtac (ballI RS ballI))),
     (excluded_middle_tac "xaa = n" 2),
     (excluded_middle_tac "x = xa" 1),
     (excluded_middle_tac "y = xa" 2),
     (excluded_middle_tac "y = xa" 1),
     (ALLGOALS (asm_simp_tac (dTerm_ss addsimps [dDeg_dAbst_lemma1]
                            addsimps succ_neq_self_simps))),
     (safe_tac (ZF_cs addSEs [lt_irrefl])),
     (etac (bspec RS bspec RS mp RS mp RS function_apply_eq) 2),
     (asm_simp_tac (nat_ss addsimps [dFV_dLift_iff]) 4),
     (subgoals_tac ["succ(xaa) ~= n", "~ succ(xaa) < n"] 1),
     (asm_simp_tac dTerm_ss 1),
     (safe_tac (ZF_cs addSIs [nat_succI, dLift_type, nat_0I])),
     (dtac (leI RS (succ_le_iff RS iffD1)) 2),
     (etac lt_irrefl 2),
     ((dtac lt_trans 1) THEN (atac 1)),
     (dtac (leI RS (succ_le_iff RS iffD1)) 1),
     (etac lt_irrefl 1)]);

qed_goal "Lsubst_eq_dsubst" dB.thy
    "LFreeForIn(B, x, A) ==> dB(Lsubst(A, x, B)) = dsubst(dB(A), x, dB(B))"
  (fn [major] =>
    [(rtac (major RS rev_mp) 1),
     (LTermOcc.ind_tac "A" [major RS LFreeForInD3] 1),
     (ALLGOALS ((rtac impI) THEN' (eresolve_tac LFreeForIn_LTermEs))),
     (subgoals_tac ["LFreeForIn(B, x, M)"] 4),
     (rtac LFreeForInI 5),
     ((etac notE 8) THEN (etac LFV_I 8)),
     (REPEAT (atac 5)),
     (TRYALL (REPEAT o ((dtac mp) THEN' atac))),
     (hyp_subst_tac 2),
     (TRYALL (REPEAT o (dtac LFreeForInD1))),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_simp_tac (LTerm_ss addsimps Lsubst_eqns
                            addsimps dB_eqns))),
     (ALLGOALS (asm_simp_tac (dTerm_ss addsimps 
                              [dB_type RS dPropD1, dB_type RS dPropD2,
                               dDeg_dLift_lemma1, dsubst_def]))),
     (rtac (dsubst_lemma2 RS sym RS function_apply_eq) 2),
     (rtac (dsubst_lemma1 RS sym RS function_apply_eq) 8),
     (rtac (dsubst_lemma1 RS sym RS function_apply_eq) 1),
     (TRYALL (REPEAT o (ares_tac [dAbst_type, dB_type, dPropD1, nat_succI,
                                nat_0I]))),
     (fast_tac ZF_cs 5),
     (etac (dB_type RS dPropD2 RS ssubst) 4),
     (rtac (Ord_0 RS le_refl) 4),
     (TRYALL ((rtac notI) THEN' (etac dFV_E))),
     (dtac dFreeIn_imp_LFreeIn 3),
     ((etac notE 4) THEN (etac LFV_I 4)),
     (etac dOcc_dAbstE 4),
     (dtac dOcc_dAbst_lemma1 1),
     (fast_tac ZF_cs 3),
     (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs) 7),
     (dtac dFreeIn_imp_LFreeIn 7),
     ((etac notE 8) THEN (etac LFV_I 8)),
     (TRYALL (REPEAT o (ares_tac [dB_type, dPropD1, nat_succI, nat_0I]))),
     (ALLGOALS (REPEAT o (etac (dB_type RS dPropE)))),
     (excluded_middle_tac "xa: dFV(dB(M))" 2),
     (excluded_middle_tac "x: dFV(dB(M))" 1),
     (ALLGOALS (asm_simp_tac (dTerm_ss addsimps 
                              [dDeg_dAbst_lemma1, dDeg_dAbst_lemma2])))]);

qed_goalw "isSubst1_isSubst2_iff" dB.thy [isSubst1_def, isSubst2_def]
    "Infinite(LVariable) ==> isSubst1(A, x, B, C) <-> isSubst2(A, x, B, C)"
  (fn [infv] =>
    [(safe_tac ZF_cs),
     (etac (LAlphaD1 RS LSkeltonEqD1) 1),
     (etac LFreeForInD1 1),
     (etac (LAlphaD1 RS LSkeltonEqD2) 1),
     (etac LFreeForInD2 1),
     (forw_inst_tac [("M", "A"), ("N", "B")] 
      (infv RS Infinite_LVariable_LAlpha_lemma) 2),
     (REPEAT (atac 2)),
     (safe_tac ZF_cs),
     (rtac exI 2),
     (REPEAT (ares_tac [conjI] 2)),
     (ALLGOALS (asm_full_simp_tac (IFOL_ss addsimps 
                            [LAlpha3_iff_LAlpha RS iff_sym]))),
     (rewrite_goals_tac [LAlpha3_def]),
     (safe_tac ZF_cs),
     (REPEAT (ares_tac [Lsubst_type] 2)),
     (rotate_tac 9 2),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss addsimps [Lsubst_eq_dsubst])))]);
