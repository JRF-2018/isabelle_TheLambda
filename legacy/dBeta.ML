(*
    File:        dBeta.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open dBeta;

qed_goal "dBeta1Rel_induct" dBeta.thy
    "[| <M, N>: dBeta1Rel; \
\     !!M N. [| M : dTerm; N : dTerm |] ==> \
\            P(dApp(dLam(M), N), dSubst(M, 0, N)); \
\     !!M M'. [| <M, M'> : dBeta1Rel; P(M, M') |] ==> \
\            P(dLam(M), dLam(M')); \
\     !!M M' N.  [| <M, M'> : dBeta1Rel; P(M, M'); N : dTerm |] ==> \
\            P(dApp(M, N), dApp(M', N)); \
\      !!M N N'. [| M : dTerm; <N, N'> : dBeta1Rel; P(N, N') |] ==> \
\            P(dApp(M, N), dApp(M, N')) |] ==> P(M, N)"
  (fn major::prems =>
    [(res_inst_tac [("P", "%x. P(x, ?X)"), ("b1", "N")]
    (fst_conv RS subst) 1),
     (res_inst_tac [("P", "%x. P(?X, x)"), ("a1", "M")]
    (snd_conv RS subst) 1),
     (rtac (major RS dBeta1Rel.induct) 1),
     (ALLGOALS (asm_full_simp_tac ZF_ss)),
     (REPEAT (fast_tac (ZF_cs addIs prems) 1))]);

qed_goalw "dBeta1_type1" dBeta.thy [dBeta1_def]
    "dBeta1(M, N) ==> M: dTerm"
  (fn [major] =>
    [(rtac ([dBeta1Rel.dom_subset, major] MRS subsetD RS SigmaD1) 1)]);

qed_goalw "dBeta1_type2" dBeta.thy [dBeta1_def]
    "dBeta1(M, N) ==> N: dTerm"
  (fn [major] =>
    [(rtac ([dBeta1Rel.dom_subset, major] MRS subsetD RS SigmaD2) 1)]);

qed_goalw "dBeta1_baseI" dBeta.thy [dBeta1_def]
    "[| A: dTerm; B: dTerm |] ==> \
\         dBeta1(dApp(dLam(A), B), dSubst(A, 0, B))"
  (fn prems =>
    [(fast_tac (ZF_cs addIs prems addIs dBeta1Rel.intrs) 1)]);

qed_goalw "dBeta1_dLamI" dBeta.thy [dBeta1_def]
    "dBeta1(M, M') ==> dBeta1(dLam(M), dLam(M'))"
  (fn prems =>
    [(fast_tac (ZF_cs addIs prems addIs dBeta1Rel.intrs) 1)]);

qed_goalw "dBeta1_dAppI1" dBeta.thy [dBeta1_def]
    "[| dBeta1(M, M'); N: dTerm |] ==> \
\          dBeta1(dApp(M, N), dApp(M', N))"
  (fn prems =>
    [(fast_tac (ZF_cs addIs prems addIs dBeta1Rel.intrs) 1)]);

qed_goalw "dBeta1_dAppI2" dBeta.thy [dBeta1_def]
    "[| M: dTerm; dBeta1(N, N') |] ==> \
\          dBeta1(dApp(M, N), dApp(M, N'))"
  (fn prems =>
    [(fast_tac (ZF_cs addIs prems addIs dBeta1Rel.intrs) 1)]);

qed_goalw "dBeta1_dVarE" dBeta.thy [dBeta1_def]
    "dBeta1(dVar(x), N) ==> R"
  (fn [major] =>
    [(cut_facts_tac [major] 1),
     (etac dBeta1Rel.elim 1),
     (safe_tac (ZF_cs addSEs dTerm.free_SEs))]);

qed_goalw "dBeta1_dBoundE" dBeta.thy [dBeta1_def]
    "dBeta1(dBound(n), N) ==> R"
  (fn [major] =>
    [(cut_facts_tac [major] 1),
     (etac dBeta1Rel.elim 1),
     (safe_tac (ZF_cs addSEs dTerm.free_SEs))]);

qed_goalw "dBeta1_dLamE" dBeta.thy [dBeta1_def]
    "[| dBeta1(dLam(M), N); \
\       !!N'. [| dBeta1(M, N'); N = dLam(N')|] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS dBeta1Rel.elim) 1),
     (rtac prem 2),
     (safe_tac (ZF_cs addSEs dTerm.free_SEs)),
     (REPEAT (ares_tac [refl] 1))]);

qed_goalw "dBeta1_dAppE" dBeta.thy [dBeta1_def]
    "[| dBeta1(dApp(A, B), N); \
\       !!x N'. [| N': dTerm; B: dTerm; \
\          A = dLam(N'); N = dSubst(N', 0, B) |] ==> R; \
\       !!A'. [| dBeta1(A, A'); B: dTerm; N = dApp(A', B) |] ==> R; \
\       !!B'. [| A: dTerm; dBeta1(B, B'); N = dApp(A, B') |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (major RS dBeta1Rel.elim) 1),
     (rtac prem3 4),
     (rtac prem2 3),
     (rtac prem1 1),
     (safe_tac (ZF_cs addSEs dTerm.free_SEs)),
     (TRYALL (rtac refl)),
     (REPEAT (atac 1))]);

val dBeta1_dTermEs = [dBeta1_dVarE, dBeta1_dBoundE,
                      dBeta1_dLamE, dBeta1_dAppE];

qed_goal "dBeta1_dAbst" dBeta.thy
    "[| dBeta1(M, M'); n: nat |] ==> \
\        dBeta1(dAbst(M, x, n), dAbst(M', x, n))"
  (fn [major, prem2] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (rtac (major RS dBeta1_type2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major RS dBeta1_type1] 1),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (safe_tac (ZF_cs addSEs dBeta1_dTermEs addSEs dTerm_typeEs
              addSEs dTerm.free_SEs)),
     (rotate_tac 7 2),
     (ALLGOALS (asm_full_simp_tac 
              (dTerm_ss addsimps [dAbst_dSubst_lemma2]))),
     (rtac dBeta1_dAppI2 4),
     (rtac dBeta1_dAppI1 3),
     (rtac dBeta1_baseI 2),
     (rtac dBeta1_dLamI 1),
     (TRYALL (REPEAT o (ares_tac [dAbst_type, nat_succI]))),
     (ALLGOALS (etac (bspec RS bspec RS mp))),
     (TRYALL (REPEAT o (ares_tac [nat_succI])))]);

qed_goal "dBeta1_dSubst" dBeta.thy
    "[| dBeta1(M, M'); N: dProp; n: nat |] ==> \
\        dBeta1(dSubst(M, n, N), dSubst(M', n, N))"
  (fn [major, prem1, prem2] =>
    [(rtac (prem1 RS dPropE) 1),
     (rtac (major RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (rtac (major RS dBeta1_type2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major RS dBeta1_type1] 1),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (safe_tac (ZF_cs addSEs dBeta1_dTermEs addSEs dTerm_typeEs
              addSEs dTerm.free_SEs)),
     (rotate_tac 8 2),
     (ALLGOALS (asm_full_simp_tac 
              (dTerm_ss addsimps [dDeg_dLift_lemma1,
                                  dSubst_dSubst_lemma2]))),
     (rtac dBeta1_dAppI2 4),
     (rtac dBeta1_dAppI1 3),
     (rtac dBeta1_baseI 2),
     (rtac dBeta1_dLamI 1),
     (TRYALL (REPEAT o (ares_tac [dSubst_type, nat_succI]))),
     (ALLGOALS (etac (bspec RS bspec RS mp))),
     (TRYALL (REPEAT o (ares_tac [nat_succI])))]);

qed_goal "dBeta1_dDeg_lemma" dBeta.thy
    "dBeta1(M, N) ==> dDeg(N) le dDeg(M)"
  (fn [major] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (major RS dBeta1_type2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major RS dBeta1_type1] 1),
     (safe_tac (ZF_cs addSEs dBeta1_dTermEs addSEs dTerm_typeEs)),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss))),
     (res_inst_tac [("M1", "N'")] (dDeg_type RS natE) 2),
     (asm_full_simp_tac (dTerm_ss addsimps [dDeg_dSubst_lemma1]) 3),
     (rtac dDeg_dSubst_lemma2 3),
     (asm_simp_tac arith_ss 4),
     (REPEAT (ares_tac [nat_0I] 2)),
     (ALLGOALS ((dtac (bspec RS mp)) THEN' (etac dBeta1_type2)
              THEN' atac)),
     (res_inst_tac [("M1", "M")] (dDeg_type RS natE) 1),
     (rotate_tac 4 2),
     (rotate_tac 4 3),
     (asm_full_simp_tac dTerm_ss 2),
     (asm_full_simp_tac dTerm_ss 2),
     (safe_tac ZF_cs),
     (TRYALL (etac le_trans)),
     (REPEAT (ares_tac [Un_upper1_le, Un_upper2_le,
                      nat_into_Ord, dDeg_type] 1))]);

qed_goal "dBeta1_dProp_lemma" dBeta.thy
    "[| dBeta1(M, N); M: dProp |] ==> N: dProp"
  (fn [major, prem] =>
    [(rtac dPropI 1),
     (rtac (major RS dBeta1_type2) 1),
     (cut_facts_tac [prem RS dPropD2, major RS dBeta1_dDeg_lemma] 1),
     (asm_full_simp_tac arith_ss 1)]);

qed_goal "dBeta1_dFV_lemma" dBeta.thy
    "dBeta1(M, N) ==> dFV(N) <= dFV(M)"
  (fn [major] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (major RS dBeta1_type2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major RS dBeta1_type1] 1),
     (safe_tac (ZF_cs addSEs dBeta1_dTermEs addSEs dTerm_typeEs)),
     (rotate_tac 7 3),
     (rotate_tac 7 4),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss))),
     (TRYALL (fn i => (dtac (bspec RS mp) i) THEN (atac (i + 1)))),
     (etac dFV_dSubst_lemma 3),
     (TRYALL ((etac dBeta1_type2) ORELSE' (ares_tac [nat_0I]))),
     (safe_tac ZF_cs),
     (ALLGOALS ((dtac subsetD) THEN' atac)),
     (safe_tac ZF_cs)]);
