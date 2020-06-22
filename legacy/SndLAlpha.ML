(*
    File:        SndLAlpha.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open SndLAlpha;

qed_goal "LAlpha2_induct" SndLAlpha.thy
    "[| <M, N>: LAlpha2; \
\     !!x. x : LVariable ==> P(LVar(x), LVar(x)); \
\     !!A B C D. [| <A, C> : LAlpha2; P(A, C); <B, D> : LAlpha2; P(B, D) |] \
\        ==> P(LApp(A, B), LApp(C, D)); \
\     !!M N x y.\
\        [| x : LVariable; y : LVariable; <M, N> : LAlpha2; P(M, N);\
\           y ~: LFV(N) - {x}; LFreeForIn(LVar(y), x, N) |] ==> \
\        P(LLam(x, M), LLam(y, Lsubst(N, x, LVar(y)))); \
\     !!A B C. \
\        [| <A, B> : LAlpha2; P(A, B); <B, C> : LAlpha2; P(B, C) |] ==> \
\           P(A, C) \
\    |] ==> P(M, N)"
  (fn major::prems =>
    [(res_inst_tac [("P", "%x. P(x, ?X)"), ("b1", "N")]
    (fst_conv RS subst) 1),
     (res_inst_tac [("P", "%x. P(?X, x)"), ("a1", "M")]
    (snd_conv RS subst) 1),
     (rtac (major RS LAlpha2.induct) 1),
     (ALLGOALS (asm_full_simp_tac ZF_ss)),
     (REPEAT (fast_tac (ZF_cs addIs prems) 1))]);

qed_goal "LAlpha2_refl" SndLAlpha.thy
    "M: LTerm ==> <M, M>: LAlpha2"
  (fn [prem] =>
    [(rtac (prem RS LTerm.induct) 1),
     (etac LAlpha2.LVarI 1),
     (etac LAlpha2.LAppI 2),
     (atac 2),
     (res_inst_tac [("P", "%x. <?X, x>: ?Y")] ssubst 1),
     (res_inst_tac [("y", "x")] LAlpha2.LLamI 2),
     (REPEAT (atac 2)),
     (asm_simp_tac ZF_ss 2),
     (etac LFreeForIn_left_LVarI 2),
     (atac 2),
     (asm_simp_tac (IFOL_ss addsimps [Lsubst_self]) 1)]);

qed_goal "LAlpha2_sym" SndLAlpha.thy
    "<M, N>: LAlpha2 ==> <N, M>: LAlpha2"
  (fn [major] =>
    [(rtac (major RS LAlpha2_induct) 1),
     (etac LAlpha2.LVarI 1),
     (etac LAlpha2.LAppI 1),
     (atac 1),
     (etac LAlpha2.transI 2),
     (atac 2),
     (forward_tac [LAlpha2.dom_subset RS subsetD] 1),
     (etac SigmaE2 1),
     (asm_full_simp_tac ZF_ss 1),
     (etac disjE 1),
     (hyp_subst_tac 2),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_self]) 2),
     (res_inst_tac [("P", "%x. <?X, x>: ?Y")] subst 2),
     (res_inst_tac [("N", "M"), ("y", "x")] LAlpha2.LLamI 3),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_self]) 2),
     (fast_tac ZF_cs 5),
     (REPEAT (ares_tac [LFreeForIn_left_LVarI] 2)),
     (res_inst_tac [("B", "LLam(x, Lsubst(Lsubst(N,x, LVar(y)), y, LVar(x)))")] 
    LAlpha2.transI 1),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_self, Lsubst_lemma2]) 2),
     (res_inst_tac [("P", "%x. <?X, x>: ?Y")] subst 2),
     (res_inst_tac [("N", "M"), ("y", "x")] LAlpha2.LLamI 3),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_self]) 2),
     (fast_tac ZF_cs 5),
     (REPEAT (ares_tac [LFreeForIn_left_LVarI] 2)),
     (rtac LAlpha2.LLamI 1),
     (REPEAT (ares_tac ([LAlpha2_refl, Lsubst_type] @ LTerm.intrs) 1)),
     (REPEAT (ares_tac [LFreeForIn_left_LVarI, LFreeForIn_name_change] 2)),
     (safe_tac (ZF_cs addSEs [LFV_E, LFreeIn_LsubstE] 
              addSEs LTermOcc.Tag.free_SEs addSEs LFreeIn_LTermEs
              addSIs LTerm.intrs))]);

qed_goal "LAlpha2_LFV_lemma" SndLAlpha.thy
    "[| <M, N>: LAlpha2; x: LFV(M) |] ==> x: LFV(N)"
  (fn [major, prem] =>
    [(rtac (prem RS rev_mp) 1),
     (rtac (major RS LAlpha2_induct) 1),
     (subgoals_tac ["A: LTerm", "B: LTerm", "C: LTerm", "D: LTerm"] 2),
     (REPEAT (eresolve_tac ([LAlpha2.dom_subset RS subsetD] RL 
                          [SigmaD1, SigmaD2]) 3)),
     (ALLGOALS (asm_simp_tac LTerm_ss)),
     (fast_tac ZF_cs 1),
     (forward_tac [LAlpha2.dom_subset RS subsetD] 1),
     (safe_tac ZF_cs),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_self]) 2),
     (REPEAT (etac LFV_E 1)),
     (rtac LFV_I 1),
     (etac LFreeIn_LsubstI1 1),
     (atac 1),
     (fast_tac ZF_cs 1)]);

qed_goal "LAlpha2_LAlpha" SndLAlpha.thy
    "<M, N>: LAlpha2 ==> LAlpha(M, N)"
  (fn [prem] =>
    [(rtac (prem RS LAlpha2_induct) 1),
     (rtac LAlpha_trans 4),
     (REPEAT (atac 4)),
     (REPEAT (ares_tac [LAlpha_LVarI, LAlpha_LAppI] 1)),
     (forward_tac [LAlpha2.dom_subset RS subsetD] 1),
     (excluded_middle_tac "y = x" 1),
     (asm_full_simp_tac ZF_ss 1),
     (safe_tac ZF_cs),
     (TRYALL (swap_res_tac [LAlpha_LLamI1])),
     (asm_simp_tac (IFOL_ss addsimps [Lsubst_self]) 2),
     (asm_simp_tac (IFOL_ss addsimps [Lsubst_self]) 3),
     (REPEAT (atac 2)),
     (rtac LAlpha_LLamI2 1),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_lemma2, Lsubst_self]) 1),
     (rtac LFreeForIn_name_change 1),
     (rtac LFV_Lsubst_notI 4),
     (REPEAT (ares_tac [LFreeForIn_left_LVarI] 1))]);

qed_goal "LAlpha_LAlpha2" SndLAlpha.thy
    "[| Infinite(LVariable); LAlpha(M, N) |] ==> <M, N>: LAlpha2"
  (fn [infv, prem] =>
    [(cut_facts_tac [prem RS LAlphaD1 RS LSkeltonEqD1] 1),
     (rtac (prem RS rev_mp) 1),
     (res_inst_tac [("x", "N")] spec 1),
     (eres_inst_tac [("M", "M")] 
      (LTermOcc.use_thm def_Terms_depth_induct) 1),
     (etac LTerm.elim 1),
     (ALLGOALS hyp_subst_tac),
     (safe_tac (ZF_cs addSEs LAlpha_LTermEs)),
     (forward_tac [depth_ind_LApp1] 3),
     (forward_tac [depth_ind_LApp2] 5),
     (rtac LAlpha2.LAppI 7),
     ((etac (bspec RS mp RS spec RS mp) 8) THEN (atac 8)),
     ((etac (bspec RS mp RS spec RS mp) 7) THEN (atac 7)),
     (REPEAT (atac 3)),
     (REPEAT (ares_tac [LAlpha2.LVarI] 1)),
     (etac (infv RS LAlpha_LLamE) 1),
     (ALLGOALS hyp_subst_tac),
    (* 16 *)
     (forward_tac [LAlphaD1 RS LSkeltonEqD2] 1),
     (res_inst_tac [("P", "%x. <?Y, x>: ?X")] ssubst 1),
     (res_inst_tac [("y", "x"), ("N", "N'")] LAlpha2.LLamI 2),
     (asm_simp_tac (IFOL_ss addsimps [Lsubst_self]) 1),
     (asm_simp_tac LTerm_ss 4),
     (forward_tac [depth_ind_LLam] 3),
     ((etac (bspec RS mp RS spec RS mp) 5) THEN (atac 5)),
     (REPEAT (ares_tac [LFreeForIn_left_LVarI] 1)),
    (* 24 *)
     (subgoals_tac ["M': LTerm", "N': LTerm", "y: LVariable",
                  "LOcc(Ma) <= domain(Z) * LTag",
                  "LOcc(M') <= domain(Z) * LTag",
                  "LOcc(N') <= domain(Z) * LTag"] 1),
     (etac (LAlphaD1 RS LSkeltonEqD2) 7),
     (etac (LAlphaD1 RS LSkeltonEqD1) 6),
     (etac LFreeForInE 5),
     (eresolve_tac LTerm_typeEs 5),
     (etac depth_ind_LLam 4),
     (rtac depth_ind_LSkeltonEq 3),
     (etac LAlphaD1 3),
     (rtac depth_ind_LSkeltonEq 2),
     (rtac LSkeltonEq_trans 2),
     (etac (LAlphaD1 RS LSkeltonEq_sym) 3),
     (rtac LSkeltonEq_Lsubst_LVar 2),
     (REPEAT (atac 2)),
     (res_inst_tac [("P", "%x. <?Y, x>: ?X")] ssubst 1),
     (rtac LAlpha2.transI 2),
     (res_inst_tac [("y", "y"), ("N", "N'")] LAlpha2.LLamI 3),
     (res_inst_tac [("y", "y"), ("N", "M'")] LAlpha2.LLamI 2),
     (rtac LAlpha2_sym 9),
     (TRYALL atac),
     ((etac (bspec RS mp RS spec RS mp) 4) THEN (atac 4)),
     ((etac (bspec RS mp RS spec RS mp) 2) THEN (atac 2)),
     (asm_simp_tac (IFOL_ss addsimps [Lsubst_self]) 1),
     (asm_simp_tac ZF_ss 3),
     (asm_simp_tac ZF_ss 5),
     (REPEAT (ares_tac [LFreeForIn_left_LVarI] 1))]);

qed_goal "LAlpha2_iff_LAlpha" SndLAlpha.thy
    "Infinite(LVariable) ==> <M,N>:LAlpha2 <-> LAlpha(M,N)"
  (fn [prem] =>
    [(rtac iffI 1),
     (etac (prem RS LAlpha_LAlpha2) 2),
     (etac LAlpha2_LAlpha 1)]);

val LAlpha2_LSkeltonEq = standard (LAlpha2_LAlpha RS LAlphaD1);

qed_goal "LAlpha2_LVarE_lemma" SndLAlpha.thy
    "<M, N>: LAlpha2 ==> M = LVar(x) --> N = LVar(x)"
  (fn [major] =>
    [(rtac (major RS LAlpha2_induct) 1),
     (safe_tac (ZF_cs addSEs LTerm.free_SEs))]);

qed_goal "LAlpha2_LVarD" SndLAlpha.thy
    "<LVar(x), N>: LAlpha2 ==>  N = LVar(x)"
  (fn [major] =>
    [(rtac (major RS LAlpha2_LVarE_lemma RS mp) 1),
     (rtac refl 1)]);

qed_goal "LAlpha2_LAppE_lemma" SndLAlpha.thy
    "<M, N>: LAlpha2 ==> \
\     (ALL A B. (M = LApp(A, B) --> \
\         (EX C D. N = LApp(C, D) & <A, C>: LAlpha2 & <B, D>: LAlpha2)))"
  (fn [major] =>
    [(rtac (major RS LAlpha2_induct) 1),
     (fast_tac (ZF_cs addSEs LTerm.free_SEs) 1),
     (fast_tac (ZF_cs addSEs LTerm.free_SEs) 2),
     (safe_tac (ZF_cs addSEs LTerm.free_SEs)),
     (TRYALL ((dtac (spec RS spec RS mp)) THEN' (rtac refl))),
     (safe_tac (ZF_cs addSEs LTerm.free_SEs)),
     (TRYALL (REPEAT o ((dtac (spec RS spec RS mp)) THEN' (rtac refl)))),
     (safe_tac (ZF_cs addSEs LTerm.free_SEs)),
     (ALLGOALS (rtac (exI RS exI))),
     (ALLGOALS (rtac (refl RS conjI))),
     (fast_tac (ZF_cs addIs [LAlpha2.transI]) 2),
     (fast_tac ZF_cs 1)]);

qed_goal "LAlpha2_LAppE" SndLAlpha.thy
    "[| <LApp(A, B), N>: LAlpha2; \
\       !! C D. [| N = LApp(C, D); <A, C>: LAlpha2; <B, D>: LAlpha2 |] ==> R \
\    |] ==> R"
  (fn [major, prem1] =>
    [(cut_facts_tac [major RS LAlpha2_LAppE_lemma] 1),
     (dtac (spec RS spec RS mp) 1),
     (rtac refl 1),
     (REPEAT (eresolve_tac [exE, conjE] 1)),
     (rtac prem1 1),
     (REPEAT (atac 1))]);

qed_goal "Lsubst_eq_LVar_lemma" SndLAlpha.thy
    "[| Lsubst(N, x, LVar(y)) = LVar(z); N: LTerm; y: LVariable; \
\       z: LVariable |] ==> N = LVar(x) & y = z  | N = LVar(x) & y = z \
\                          | N = LVar(z) & x ~= z"
  (fn major::sub::prems =>
    [(cut_facts_tac (major::sub::prems) 1),
     (rtac (sub RS LTerm.elim) 1),
     (excluded_middle_tac "x = xa" 2),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (rotate_tac 1)),
     (TRYALL (REPEAT o hyp_subst_tac)),
     (ALLGOALS (asm_full_simp_tac LTerm_ss)),
     (safe_tac (ZF_cs addSEs LTerm.free_SEs))]);

qed_goal "Lsubst_eq_LLam_lemma" SndLAlpha.thy
    "[| Lsubst(N, x, LVar(y)) = LLam(x, M); N: LTerm; M: LTerm; \
\       y: LVariable |] ==> N = LLam(x, M)"
  (fn major::sub::prems =>
    [(cut_facts_tac (major::sub::prems) 1),
     (rtac (sub RS LTerm.elim) 1),
     (excluded_middle_tac "x = xa" 2),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (rotate_tac 1)),
     (TRYALL (REPEAT o hyp_subst_tac)),
     (ALLGOALS (asm_full_simp_tac LTerm_ss)),
     (safe_tac (ZF_cs addSEs LTerm.free_SEs))]);

qed_goal "LAlpha2_LLam_LVar_lemma1" SndLAlpha.thy
    "[| <M, N>: LAlpha2; LVariable = {x, y}; y ~= x |] \
\        ==> M = LLam(y, LVar(x)) --> N = LLam(y, LVar(x))"
  (fn major::prems =>
    [(cut_facts_tac prems 1),
     (rtac (major RS LAlpha2_induct) 1),
     (asm_full_simp_tac ZF_ss 3),
     (REPEAT (fast_tac (ZF_cs addSEs LTerm.free_SEs) 4)),
     (REPEAT (fast_tac (ZF_cs addSEs LTerm.free_SEs) 1)),
     (forward_tac [LAlpha2.dom_subset RS subsetD] 1),
     (etac SigmaE2 1),
     (etac disjE 1),
     (hyp_subst_tac 2),
     (ALLGOALS (rtac impI)),
     (ALLGOALS (REPEAT o ((eresolve_tac LTerm.free_SEs) ORELSE'
                        (dtac LAlpha2_LVarD) ORELSE'
                        hyp_subst_tac))),
     (ALLGOALS (asm_full_simp_tac (LTerm_ss addsimps [Lsubst_self]))),
     (fast_tac ZF_cs 1)]);

qed_goal "LAlpha2_LLam_LLam_LVar_lemma1" SndLAlpha.thy
    "[| <M, N>: LAlpha2; LVariable = {x, y}; y ~= x |] \
\        ==> M = LLam(x, LLam(y, LVar(x))) \
\         --> N = LLam(x, LLam(y, LVar(x)))"
  (fn major::prems =>
    [(cut_facts_tac prems 1),
     (rtac (major RS LAlpha2_induct) 1),
     (asm_full_simp_tac ZF_ss 3),
     (REPEAT (fast_tac (ZF_cs addSEs LTerm.free_SEs) 4)),
     (REPEAT (fast_tac (ZF_cs addSEs LTerm.free_SEs) 1)),
     (forward_tac [LAlpha2.dom_subset RS subsetD] 1),
     (etac SigmaE2 1),
     (etac disjE 1),
     (hyp_subst_tac 2),
     (ALLGOALS (rtac impI)),
     (ALLGOALS (REPEAT o ((eresolve_tac LTerm.free_SEs) ORELSE'
                        hyp_subst_tac))),
     (ALLGOALS (asm_full_simp_tac (LTerm_ss addsimps [Lsubst_self]))),
    (* 12 *)
     (ALLGOALS (dtac LAlpha2_LLam_LVar_lemma1)),
     (TRYALL atac),
     (ALLGOALS ((dtac mp) THEN' (rtac refl))),
     (ALLGOALS (REPEAT o hyp_subst_tac)),
     (rtac refl 2),
     (asm_full_simp_tac LTerm_ss 1),
     (etac disjE 1),
     (hyp_subst_tac 2),
     (safe_tac (ZF_cs addSEs LFreeForIn_LTermEs)),
     (ALLGOALS (asm_full_simp_tac LTerm_ss)),
     (safe_tac ZF_cs)]);

qed_goal "LAlpha2_LLam_LLam_LVar_lemma" SndLAlpha.thy
    "[| LVariable = {x, y}; y ~= x |] ==> \
\          <LLam(x, LLam(y, LVar(x))), LLam(y, LLam(x, LVar(y)))>~: LAlpha2"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac notI 1),
     (dtac LAlpha2_LLam_LLam_LVar_lemma1 1),
     (dtac mp 3),
     (REPEAT (ares_tac [refl] 1)),
     (safe_tac (ZF_cs addSEs LTerm.free_SEs))]);

qed_goal "LAlpha_LLam_LLam_LVar_lemma" SndLAlpha.thy
    "[| LVariable = {x, y}; y ~= x |] ==> \
\          LAlpha(LLam(x, LLam(y, LVar(x))), LLam(y, LLam(x, LVar(y))))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac LAlphaI 1),
     (REPEAT ((ares_tac ([consI1, consI2] @ LSkeltonEq_LTermIs) 1) ORELSE
            (CHANGED (asm_simp_tac IFOL_ss 1)))),
     (safe_tac (ZF_cs addSEs LFreeIn_LTermEs addSEs LBoundBy_LTermEs
              addSEs LTermOcc.Tag.free_SEs)),
     (REPEAT (ares_tac ([exI] @ LBoundBy_LTermIs @ LFreeIn_LTermIs) 1))]);
