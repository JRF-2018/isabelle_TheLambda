(*
    File:        Lambda.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open Lambda;

val LAlpha_LLamE2 = Infinite_LVariable RS LAlpha_LLamE;
val LAlpha_LTermEs2 = [LAlpha_LVarE, LAlpha_LLamE2,
                      LAlpha_LAppE];


(** LAQ: LAlpha-quotient **)
qed_goalw "LAQ_I" Lambda.thy [LAQ_def]
    "LAlpha(M, N) ==> N: LAQ(M)"
  (fn [major] =>
    [(rtac CollectI 1),
     (rtac (major RS LAlphaD1 RS LSkeltonEqD2) 1),
     (rtac major 1)]);

qed_goalw "LAQ_D" Lambda.thy [LAQ_def]
    "N: LAQ(M) ==> LAlpha(M, N)"
  (fn [major] =>
    [(rtac (major RS CollectE) 1),
     (atac 1)]);

qed_goal "LAQ_self" Lambda.thy
    "M: LTerm ==> M: LAQ(M)"
  (fn [major] =>
    [(rtac LAQ_I 1),
     (rtac (major RS LAlpha_refl) 1)]);

qed_goal "LAQ_eqI" Lambda.thy
    "LAlpha(M, N) ==> LAQ(M) = LAQ(N)"
  (fn [major] =>
    [(safe_tac (eq_cs addSDs [LAQ_D] addSIs [LAQ_I])),
     (etac ((major RS LAlpha_sym) RS LAlpha_trans) 1),
     (etac (major RS LAlpha_trans) 1)]);

qed_goal "LAQ_eqD" Lambda.thy
    "[| LAQ(M) = LAQ(N); M: LTerm |] ==> LAlpha(M, N)"
  (fn [major,prem] =>
    [(rtac (major RS equalityE) 1),
     ((dtac subsetD 1) THEN (rtac (prem RS LAQ_self) 1)),
     (etac (LAQ_D RS LAlpha_sym) 1)]);


(** Term **)
qed_goalw "TermI" Lambda.thy [Term_def]
    "[| m: LTerm; M = LAQ(m) |] ==> M: Term"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (fast_tac ZF_cs 1)]);

qed_goal "LAQ_type" Lambda.thy
    "m: LTerm ==> LAQ(m): Term"
  (fn [major] =>
    [(REPEAT (ares_tac [TermI, refl, major] 1))]);

qed_goalw "TermE" Lambda.thy [Term_def]
    "[| M: Term; \
\       !! m. [| M = LAQ(m); m: LTerm |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS RepFunE) 1),
     (REPEAT (ares_tac [prem] 1))]);

qed_goal "Term_LFreeForInE" Lambda.thy
    "[| M: Term; x: LVariable; n: LTerm; \
\       !!m. [| M = LAQ(m); m: LTerm; LFreeForIn(n, x, m) |] ==> R |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (major RS TermE) 1),
     (rtac (Infinite_LVariable RS Infinite_LVariable_LAlpha_lemma RS bexE) 1),
     (rtac prem1 2),
     (rtac prem2 2),
     (atac 1),
     (rtac prem3 1),
     (safe_tac (ZF_cs addSDs [LAQ_eqI])),
     (REPEAT (atac 1))]);

qed_goal "Term_LFreeForInE2" Lambda.thy
    "[| M: Term; x: LVariable; X: Fin(LTerm); \
\       !!m. [| M = LAQ(m); m: LTerm; ALL n: X. LFreeForIn(n, x, m) |] \
\             ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (major RS TermE) 1),
     (rtac (Infinite_LVariable RS Infinite_LVariable_LAlpha_lemma2 RS bexE) 1),
     (rtac prem1 2),
     (rtac prem2 2),
     (atac 1),
     (rtac prem3 1),
     (safe_tac (ZF_cs addSDs [LAQ_eqI])),
     (etac bspec 3),
     (REPEAT (atac 1))]);

qed_goalw "LAQ_LVar" Lambda.thy [Var_def]
    "x: LVariable ==> LAQ(LVar(x)) = Var(x)"
  (fn [major] =>
    [(fast_tac (eq_cs addIs [major, LAlpha_LVarI]
              addSDs [LAQ_D] addSIs [LAQ_I] addSEs LAlpha_LTermEs2) 1)]);

qed_goalw "LAQ_LLam" Lambda.thy [Lam_def]
    "[| x: LVariable; m: LTerm |] ==> LAQ(LLam(x, m)) = Lam(x, LAQ(m))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSDs [LAQ_D] addSIs LTerm.intrs
                addSEs [TermE] addSIs [LAQ_type, LAQ_I] 
                addSEs LAlpha_LTermEs2)),
     (etac (LAlphaD1 RS LSkeltonEqD2) 1),
     (etac (LAlphaD1 RS LSkeltonEqD1) 3),
     (dtac LFreeForInD1 2),
     (eresolve_tac LTerm_typeEs 2),
     (atac 2),
     (rtac bexI 1),
     (REPEAT (ares_tac [LAQ_self, LAlpha_sym RS LAlpha_LLamI1] 1)),
     (dtac LAlpha_LLamI2 1),
     (rtac bexI 3),
     (REPEAT (ares_tac [LAQ_I] 1)),
     (rtac LAlpha_trans 1),
     (etac LAlpha_sym 2),
     (etac LAlpha_LLamI1 1),
     (atac 1)]);

qed_goalw "LAQ_LApp" Lambda.thy [App_def]
    "[| m: LTerm; n: LTerm |] ==> LAQ(LApp(m, n)) = App(LAQ(m), LAQ(n))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (fast_tac (eq_cs addSDs [LAQ_D] addSIs LTerm.intrs 
              addIs LAlpha_LTermIs addSEs [TermE]
              addIs ([LAlphaD1] RL [LSkeltonEqD1, LSkeltonEqD2])
              addSIs [LAQ_I, LAQ_type] addSEs LAlpha_LTermEs2) 1)]);

val Term_LAQ = [LAQ_LVar, LAQ_LLam, LAQ_LApp] RL [sym];

qed_goal "Term_VarI" Lambda.thy
    "x: LVariable ==> Var(x): Term"
  (fn [major] =>
    [(rtac (major RS LAQ_LVar RS subst) 1),
     (rtac TermI 1),
     (rtac refl 2),
     (resolve_tac ([major] RL LTerm.intrs) 1)]);

qed_goal "Term_LamI" Lambda.thy
    "[| x: LVariable; M: Term |] ==> Lam(x, M): Term"
  (fn [prem1, prem2] =>
    [(rtac (prem2 RS TermE) 1),
     (hyp_subst_tac 1),
     (rtac (prem1 RS LAQ_LLam RS subst) 1),
     (atac 1),
     (rtac TermI 1),
     (rtac refl 2),
     (REPEAT (ares_tac ([prem1] @ LTerm.intrs) 1))]);

qed_goal "Term_AppI" Lambda.thy
    "[| M: Term; N: Term |] ==> App(M, N): Term"
  (fn [prem1, prem2] =>
    [(rtac (prem1 RS TermE) 1),
     (rtac (prem2 RS TermE) 1),
     (REPEAT (hyp_subst_tac 1)),
     (rtac (LAQ_LApp RS subst) 1),
     (rtac TermI 3),
     (rtac refl 4),
     (REPEAT (ares_tac LTerm.intrs 1))]);

val Term_intrs = [Term_VarI, Term_LamI, Term_AppI];

qed_goalw "Term_VarD" Lambda.thy [Var_def]
    "Var(x): Term ==> x: LVariable"
  (fn [major] =>
    [(rtac (major RS TermE) 1),
     (dtac equalityD1 1),
     (dtac (singletonI RSN (2, subsetD)) 1),
     (dtac LAQ_D 1),
     (etac (LAlpha_sym RS LAlpha_LVarE) 1),
     (atac 1)]);

qed_goalw "Term_LamE" Lambda.thy [Lam_def]
    "[| Lam(x, M): Term; \
\       [| x: LVariable; M: Term |] ==> R |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS TermE) 1),
     (rtac prem 1),
     (dtac equalityD2 2),
     (dtac (LAQ_self RSN (2, subsetD)) 2),
     (dtac equalityD2 1),
     (dtac (LAQ_self RSN (2, subsetD)) 1),
     (safe_tac ZF_cs),
     (dtac (LAlphaD1 RS LSkeltonEqD2) 1),
     (eresolve_tac LTerm_typeEs 1),
     (atac 1)]);

qed_goalw "Term_AppE" Lambda.thy [App_def]
    "[| App(M, N): Term; \
\      [| M: Term; N: Term |] ==> R |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS TermE) 1),
     (dtac equalityD2 1),
     (dtac (LAQ_self RSN (2, subsetD)) 1),
     (rtac prem 2),
     (safe_tac ZF_cs)]);

val Term_typeEs = [make_elim Term_VarD, Term_LamE, Term_AppE];

qed_goal "Term_elim" Lambda.thy
    "[| M: Term; \
\       !! x. [| x: LVariable; M = Var(x) |] ==> R; \
\       !! x N. [| x: LVariable; N: Term; M = Lam(x, N) |] ==> R; \
\       !! A B. [| A: Term; B: Term; M = App(A, B) |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (major RS TermE) 1),
     (etac LTerm.elim 1),
     (rtac prem3 3),
     (rtac prem2 2),
     (rtac prem1 1),
     (ALLGOALS hyp_subst_tac),
     (TRYALL (resolve_tac (Term_LAQ RL [sym]))),
     (REPEAT (ares_tac [LAQ_type] 1))]);

qed_goal "Term_induct" Lambda.thy
    "[| M: Term; \
\       !! x. x: LVariable ==> P(Var(x)); \
\       !! x N. [| x: LVariable; N: Term; P(N) |] ==> P(Lam(x, N)); \
\       !! A B. [| A: Term; P(A); B: Term; P(B) |] ==> P(App(A, B)) \
\    |] ==> P(M)"
  (fn major::prems =>
    [(rtac (major RS TermE) 1),
     (etac rev_mp 1),
     (res_inst_tac [("x", "M")] spec 1),
     (LTermOcc.ind_tac "m" [] 1),
     (safe_tac ZF_cs),
     (TRYALL (REPEAT o ((dtac (spec RS mp)) THEN' (rtac refl)))),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps (Term_LAQ RL [sym])))),
     (REPEAT (ares_tac ([LAQ_type] @ prems) 1))]);

(** FV **)
qed_goalw "FV_LAQ" Lambda.thy [FV_def]
    "m: LTerm ==> FV(LAQ(m)) = LFV(m)"
  (fn [major] =>
    [(rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [LFV_E, make_elim LAQ_D] addSIs [LAQ_I])),
     (rtac RepFunI 3),
     (rtac (major RS LAQ_self) 3),
     (rtac LFV_I 2),
     (etac LAlphaD2 2),
     (atac 2),
     (etac INT_E 1),
     (rtac (major RS LAQ_self) 1)]);

qed_goal "FV_Var" Lambda.thy
    "x: LVariable ==> FV(Var(x)) = {x}"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ addsimps [FV_LAQ]) 1)]);

qed_goal "FV_Lam" Lambda.thy
    "[| x: LVariable; M: Term |] ==> FV(Lam(x, M)) = FV(M) - {x}"
  (fn [prem1, prem2] =>
    [(rtac (prem2 RS TermE) 1),
     (cut_facts_tac [prem1] 1),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ addsimps [FV_LAQ]) 1)]);

qed_goal "FV_App" Lambda.thy
    "[| M: Term; N: Term |] ==> FV(App(M, N)) = FV(M) Un FV(N)"
  (fn [prem1, prem2] =>
    [(rtac (prem1 RS TermE) 1),
     (rtac (prem2 RS TermE) 1),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ addsimps [FV_LAQ]) 1)]);

val FV_eqns = [FV_Var, FV_App, FV_Lam];


(** subst **)
qed_goalw "subst_LAQ" Lambda.thy [subst_def]
    "[| LFreeForIn(n, x, m) |] ==> \
\       subst(LAQ(m), x, LAQ(n)) = LAQ(Lsubst(m, x, n))"
  (fn [major] =>
    [(cut_facts_tac ([major] RL 
                   [LFreeForInD1, LFreeForInD2, LFreeForInD3]) 1),
     (cut_facts_tac [major] 1),
     (safe_tac (eq_cs addSEs LAlpha_LTermEs2 addSEs LTerm.free_SEs
              addSDs [LAQ_D] addSIs [LAQ_I])),
     (rtac LAlpha_trans 1),
     (atac 2),
     (REPEAT (ares_tac [LAlpha_LsubstI] 1)),
     (etac (LAlphaD1 RS LSkeltonEqD2) 1),
     (REPEAT (ares_tac [exI, LAQ_self, conjI] 1))]);

qed_goal "subst_type" Lambda.thy
    "[| M: Term; x: LVariable; N: Term |] ==> subst(M, x, N): Term"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem3 RS TermE) 1),
     (rtac ([prem1, prem2] MRS Term_LFreeForInE) 1),
     (atac 1),
     (asm_simp_tac (ZF_ss addsimps [subst_LAQ]) 1),
     (REPEAT (ares_tac [LAQ_type, Lsubst_type, prem2] 1))]);

qed_goal "subst_Var1" Lambda.thy
    "[| x: LVariable; N: Term |] ==> subst(Var(x), x, N) = N"
  (fn [prem1, prem2] =>
    [(cut_facts_tac [prem1] 1),
     (rtac (prem2 RS TermE) 1),
     (asm_simp_tac (ZF_ss addsimps Term_LAQ) 1),
     (rtac (subst_LAQ RS trans) 1),
     (REPEAT (ares_tac LFreeForIn_LTermIs 1)),
     (asm_simp_tac LTerm_ss 1)]);

qed_goal "subst_Var2" Lambda.thy
    "[| x ~= y; y: LVariable; x: LVariable; N: Term |] \
\        ==> subst(Var(y), x, N) = Var(y)"
  (fn [prem1, prem2, prem3, prem4] =>
    [(cut_facts_tac [prem1, prem2, prem3] 1),
     (rtac (prem4 RS TermE) 1),
     (asm_simp_tac (ZF_ss addsimps Term_LAQ) 1),
     (rtac (subst_LAQ RS trans) 1),
     (REPEAT (ares_tac LFreeForIn_LTermIs 1)),
     (asm_simp_tac LTerm_ss 1)]);

qed_goal "subst_Lam1" Lambda.thy
    "[| x: LVariable; M: Term; N: Term |] \
\        ==> subst(Lam(x, M), x, N) = Lam(x, M)"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem3 RS TermE) 1),
     (rtac (prem2 RS TermE) 1),
     (cut_facts_tac [prem1] 1),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ) 1),
     (rtac (subst_LAQ RS trans) 1),
     (rtac LFreeForIn_LLamI1 1),
     (asm_simp_tac LTerm_ss 4),
     (REPEAT (atac 1))]);

qed_goal "subst_Lam2" Lambda.thy
    "[| x: LVariable; y: LVariable; M: Term; N: Term; y ~= x; x ~: FV(N) |] \
\        ==> subst(Lam(x, M), y, N) = Lam(x, subst(M, y, N))"
  (fn [prem0, prem1, prem2, prem3, prem4, prem5] =>
    [(rtac (prem3 RS TermE) 1),
     (rtac ([prem2, prem1] MRS Term_LFreeForInE) 1),
     (atac 1),
     (cut_facts_tac [prem0, prem1, prem4, prem5] 1),
     (asm_full_simp_tac (LTerm_ss addsimps Term_LAQ 
                       addsimps [subst_LAQ, FV_LAQ]) 1),
     (rtac (subst_LAQ RS trans) 1),
     (asm_simp_tac LTerm_ss 2),
     (rtac LFreeForIn_LLamI2 1),
     (fast_tac ZF_cs 3),
     (REPEAT (atac 1))]);

qed_goal "subst_App" Lambda.thy
    "[| A: Term; B: Term; x: LVariable; N: Term |] \
\        ==> subst(App(A, B), x, N) = App(subst(A, x, N), subst(B, x, N))"
  (fn [prem1, prem2, prem3, prem4] =>
    [(rtac (prem4 RS TermE) 1),
     (rtac ([prem1, prem3] MRS Term_LFreeForInE) 1),
     (atac 1),
     (rtac ([prem2, prem3] MRS Term_LFreeForInE) 1),
     (atac 1),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ addsimps 
                  [LFreeForIn_LAppI, subst_LAQ]) 1)]);

qed_goal "subst_self" Lambda.thy
    "[| M: Term; x: LVariable |] ==> subst(M, x, Var(x)) = M"
  (fn [prem1, prem2] =>
    [(res_inst_tac [("n", "LVar(x)")] 
    ([prem1, prem2] MRS Term_LFreeForInE) 1),
     (resolve_tac ([prem2] RL LTerm.intrs) 1),
     (cut_facts_tac [prem2] 1),
     (asm_full_simp_tac (LTerm_ss addsimps Term_LAQ 
                       addsimps [subst_LAQ, Lsubst_self]) 1)]);

qed_goal "subst_lemma2" Lambda.thy
    "[| M: Term; N: Term; x: LVariable; y: LVariable; y ~: FV(M) |] ==> \
\      subst(subst(M, x, Var(y)), y, N) = subst(M, x, N)"
  (fn [prem1, prem2, prem3, prem4, prem5] =>
    [(rtac (prem2 RS TermE) 1),
     (res_inst_tac [("X", "{LVar(y), m}")] 
      ([prem1, prem3] MRS Term_LFreeForInE2) 1),
     (REPEAT (ares_tac ([prem4] @ LTerm.intrs @ Fin.intrs) 1)),
     (cut_facts_tac [prem3, prem4, prem5] 1),
     (asm_full_simp_tac (LTerm_ss addsimps Term_LAQ 
                       addsimps [subst_LAQ, FV_LAQ]) 1),
     (etac conjE 1),
     (rtac (subst_LAQ RS trans) 1),
     (REPEAT (ares_tac [LFreeForIn_name_change] 1)),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_lemma2]) 1)]);

val subst_eqns = [subst_Var1, subst_Var2, subst_App, subst_Lam1, 
                  subst_Lam2, subst_self, subst_lemma2];


(** Term.free_iffs **)
qed_goalw "Var_iff" Lambda.thy [Var_def]
    "Var(x) = Var(y) <-> x = y"
  (fn _ =>
    [(asm_simp_tac (IFOL_ss addsimps [singleton_iff2]) 1),
     (fast_tac (ZF_cs addSEs LTerm.free_SEs) 1)]);

qed_goal "App_eqD" Lambda.thy
    "[| App(A, B) = App(A', B'); A: Term; B: Term |] \
\        ==> A = A' & B = B'"
  (fn major::prems =>
    [(cut_facts_tac prems 1),
     (subgoals_tac ["App(A', B'): Term"] 1),
     (rtac (major RS subst) 2),
     (REPEAT (ares_tac Term_intrs 2)),
     (etac Term_AppE 1),
     (REPEAT (etac TermE 1)),
     (cut_facts_tac [major] 1),
     (REPEAT (hyp_subst_tac 1)),
     (asm_full_simp_tac (IFOL_ss addsimps Term_LAQ) 1),
     (dtac LAQ_eqD 1),
     (safe_tac (ZF_cs addSIs LTerm.intrs addSEs LAlpha_LTermEs2
              addSEs LTerm.free_SEs)),
     (REPEAT (etac LAQ_eqI 1))]);

qed_goal "App_iff" Lambda.thy
    "[| A: Term; B: Term |] ==> \
\        App(A, B) = App(A', B') <-> A = A' & B = B'"
  (fn prems =>
    [(rtac iffI 1),
     (etac App_eqD 1),
     (REPEAT (ares_tac prems 1)),
     (fast_tac ZF_cs 1)]);

qed_goal "Lam_eqD" Lambda.thy
    "[| Lam(x, M) = Lam(y, M'); x: LVariable; M: Term; \
\       y: LVariable; M': Term \
\    |] ==> M = subst(M', y, Var(x)) & x ~: FV(M') - {y}"
  (fn [major, prem1, prem2, prem3, prem4] =>
    [(rtac (prem2 RS TermE) 1),
     (res_inst_tac [("n", "LVar(x)")] 
    ([prem4, prem3] MRS Term_LFreeForInE) 1),
     (resolve_tac ([prem1] RL LTerm.intrs) 1),
     (cut_facts_tac [prem1, prem3, major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps Term_LAQ 
                       addsimps [subst_LAQ, FV_LAQ]) 1),
     (dtac (LAQ_eqD RS LAlpha_sym) 1),
     (safe_tac (ZF_cs addSIs LTerm.intrs addSEs LAlpha_LTermEs2
              addSEs LTerm.free_SEs)),
     (etac LFV_E 3),
     (etac swap 3),
     ((dtac LAlphaD2 3) THEN (atac 3)),
     (etac LFV_I 3),
     (ALLGOALS (rtac LAQ_eqI)),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_self]) 1),
     (etac LAlpha_sym 1),
     (etac LAlpha_trans 1),
     (rtac LAlpha_LsubstI 1),
     (etac LAlpha_sym 1),
     (REPEAT (ares_tac [LAlpha_LVarI] 1))]);

qed_goal "Alpha" Lambda.thy
    "[| M: Term; x: LVariable; y: LVariable; x ~: FV(M) - {y}|] ==> \
\     Lam(y, M) = Lam(x, subst(M, y, Var(x)))"
  (fn [prem1, prem2, prem3, prem4] =>
    [(res_inst_tac [("n", "LVar(x)")] 
    ([prem1, prem3] MRS Term_LFreeForInE) 1),
     (resolve_tac ([prem2] RL LTerm.intrs) 1),
     (cut_facts_tac [prem2, prem3, prem4] 1),
     (asm_full_simp_tac (LTerm_ss addsimps Term_LAQ 
                       addsimps [subst_LAQ, FV_LAQ]) 1),
     (rtac LAQ_eqI 1),
     (etac disjE 1),
     (hyp_subst_tac 2),
     (asm_simp_tac (LTerm_ss addsimps [Lsubst_self]) 2),
     (rtac LAlpha_LLamI3 1),
     (REPEAT (ares_tac ([LAlpha_refl] @ LTerm.intrs) 1))]);

qed_goal "Lam_iff" Lambda.thy
    "[| M: Term; N: Term; x: LVariable; y: LVariable |] ==> \
\      Lam(x, M) = Lam(y, N) <-> M = subst(N, y, Var(x)) & x ~: FV(N) - {y}"
  (fn prems =>
    [(rtac iffI 1),
     (etac Lam_eqD 1),
     (REPEAT (ares_tac prems 1)),
     (etac conjE 1),
     (hyp_subst_tac 1),
     (rtac (Alpha RS sym) 1),
     (REPEAT (ares_tac prems 1))]);

val Term_free_iffs = [Var_iff, App_iff, Lam_iff] @
    (map (fn (s, t) => prove_goal Lambda.thy t
          (fn prems =>
           [(cut_facts_tac prems 1),
            (safe_tac ZF_cs),
            (subgoal_tac s 1),
            (etac subst 2),
            (REPEAT (ares_tac Term_intrs 2)),
            (eresolve_tac Term_typeEs 1),
            (REPEAT (etac TermE 1)),
            (rotate_tac 2 1),
            (asm_full_simp_tac 
             (IFOL_ss addsimps Term_LAQ) 1),
            (dtac LAQ_eqD 1),
            (safe_tac (ZF_cs addSIs LTerm.intrs 
                       addSEs LTerm.free_SEs
                       addSEs LAlpha_LTermEs2))]))
    [("Lam(y, M): Term", 
      "x: LVariable ==> Var(x) = Lam(y, M) <-> False"),
     ("App(M, N): Term",
      "x: LVariable ==> Var(x) = App(M, N) <-> False"),
     ("Var(y): Term",
      "[| x: LVariable; M: Term |] ==> Lam(x, M) = Var(y) <-> False"),
     ("App(A, B): Term",
      "[| x: LVariable; M: Term |] ==> Lam(x, M) = App(A, B) <-> False"),
     ("Var(y): Term",
      "[| M: Term; N: Term |] ==> App(M, N) = Var(y) <-> False"),
     ("Lam(x, M): Term",
      "[| A: Term; B: Term |] ==> App(A, B) = Lam(x, M) <-> False")]);


(** Beta1 **)
qed_goalw "Beta1D1" Lambda.thy [Beta1_def]
    "Beta1(M, N) ==> M: Term"
  (fn [major] =>
    [(rtac (major RS conjunct1) 1)]);

qed_goalw "Beta1D2" Lambda.thy [Beta1_def]
    "Beta1(M, N) ==> N: Term"
  (fn [major] =>
    [(rtac (major RS conjunct2 RS conjunct1) 1)]);

qed_goalw "Beta1_baseI" Lambda.thy [Beta1_def]
    "[| M: Term; x: LVariable; N: Term |] \
\       ==> Beta1(App(Lam(x, M), N), subst(M, x, N))"
  (fn [prem1, prem2, prem3] =>
    [(REPEAT (ares_tac (Term_intrs @ [prem1, prem2, prem3, 
                                    conjI, subst_type]) 1)),
     (rtac (prem3 RS TermE) 1),
     (rtac ([prem1, prem2] MRS Term_LFreeForInE) 1),
     (atac 1),
     (cut_facts_tac [prem2] 1),
     (asm_full_simp_tac (LTerm_ss addsimps Term_LAQ
                       addsimps [subst_LAQ]) 1),
     (REPEAT (ares_tac (LTerm.intrs @ [bexI, LBeta1_baseI, LAQ_self, 
                                     Lsubst_type]) 1))]);

qed_goalw "Beta1_LamI" Lambda.thy [Beta1_def]
    "[| Beta1(M, M'); x: LVariable |]  ==> \
\         Beta1(Lam(x, M), Lam(x, M'))"
  (fn [prem1, prem2] =>
    [(cut_facts_tac [prem1, prem2] 1),
     (safe_tac (ZF_cs addSIs Term_intrs)),
     (REPEAT (etac TermE 1)),
     (REPEAT (hyp_subst_tac 1)),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ) 1),
     (REPEAT (dtac LAQ_D 1)),
     (rtac bexI 1),
     (rtac bexI 1),
     (rtac LBeta1_LLamI 1),
     (REPEAT (ares_tac [LAQ_I, LAlpha_LLamI1] 1))]);

qed_goalw "Beta1_AppI1" Lambda.thy [Beta1_def]
    "[| Beta1(M, M'); N: Term |]  ==> \
\         Beta1(App(M, N), App(M', N))"
  (fn [prem1, prem2] =>
    [(cut_facts_tac [prem1, prem2] 1),
     (safe_tac (ZF_cs addSIs Term_intrs)),
     (REPEAT (etac TermE 1)),
     (REPEAT (hyp_subst_tac 1)),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ) 1),
     (REPEAT (dtac LAQ_D 1)),
     (rtac bexI 1),
     (rtac bexI 1),
     (rtac LBeta1_LAppI1 1),
     (REPEAT (ares_tac [LAQ_I, LAlpha_LAppI, LAlpha_refl] 1))]);

qed_goalw "Beta1_AppI2" Lambda.thy [Beta1_def]
    "[| Beta1(N, N'); M: Term |]  ==> \
\         Beta1(App(M, N), App(M, N'))"
  (fn [prem1, prem2] =>
    [(cut_facts_tac [prem1, prem2] 1),
     (safe_tac (ZF_cs addSIs Term_intrs)),
     (REPEAT (etac TermE 1)),
     (REPEAT (hyp_subst_tac 1)),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ) 1),
     (REPEAT (dtac LAQ_D 1)),
     (rtac bexI 1),
     (rtac bexI 1),
     (rtac LBeta1_LAppI2 1),
     (REPEAT (ares_tac [LAQ_I, LAlpha_LAppI, LAlpha_refl] 1))]);

qed_goalw "Beta1_VarE" Lambda.thy [Beta1_def]
    "Beta1(Var(x), N) ==> R"
  (fn [major] =>
    [(cut_facts_tac [major] 1),
     (safe_tac (ZF_cs addSEs Term_typeEs)),
     (rotate_tac 2 1),
     (asm_full_simp_tac (IFOL_ss addsimps Term_LAQ) 1),
     (safe_tac (ZF_cs addSDs [LAQ_D] addSEs LAlpha_LTermEs2
              addSEs LBeta1_LTermEs))]);

qed_goalw "Beta1_LamE1" Lambda.thy [Beta1_def]
    "[| Beta1(Lam(x, M), N); \
\       !!N'. [| x: LVariable; N = Lam(x, N'); Beta1(M, N')|] \
\          ==> R; \
\       !!y N'. [| x: LVariable; y: LVariable; M: Term; N': Term; y ~: FV(M); \
\           N = Lam(y, N'); Beta1(subst(M, x, Var(y)), N')|] \
\          ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac (Term_typeEs @ [conjE, bexE, TermE]) 1)),
     (rotate_tac 3 1),
     (asm_full_simp_tac (IFOL_ss addsimps Term_LAQ) 1),
     (REPEAT (dtac LAQ_D 1)),
     (eresolve_tac LAlpha_LTermEs2 1),
     (ALLGOALS bound_hyp_subst_tac),
     (ALLGOALS (eresolve_tac LBeta1_LTermEs)),
     (ALLGOALS bound_hyp_subst_tac),
     (res_inst_tac [("y", "y"), ("N'", "LAQ(N'a)")] prem2 2),
     (res_inst_tac [("N'", "LAQ(N'a)")] prem1 1),
     (safe_tac (ZF_cs addSIs [subst_type, LAQ_type]
              addSIs Term_intrs)),
     (TRYALL (etac LBeta1_type2)),
     (dres_inst_tac [("M", "ma")] LAQ_eqI 5),
     (ALLGOALS (asm_full_simp_tac (LTerm_ss addsimps Term_LAQ
                                 addsimps [FV_LAQ, LBeta1_type2, 
                                           subst_LAQ]))),
     (etac LAQ_eqI 1),
     (etac LAQ_eqI 3),
     (etac LFV_E 2),
     ((dtac LAlphaD2 2) THEN (atac 2)),
     ((etac notE 2) THEN (etac LFV_I 2)),
     (ALLGOALS (REPEAT o ((ares_tac [bexI, LAQ_self, LAQ_I]) ORELSE'
                        (etac LBeta1_type2) ORELSE'
                        (etac LAlpha_sym))))]);

qed_goalw "Beta1_AppE1" Lambda.thy [Beta1_def]
    "[| Beta1(App(A, B), N); \
\       !!x N'. [| x: LVariable; N': Term; B: Term; \
\          A = Lam(x, N'); N = subst(N', x, B) |] ==> R; \
\       !!A'. [| N = App(A',B); Beta1(A, A'); B: Term |] ==> R; \
\       !!B'. [| N = App(A, B'); Beta1(B, B'); A: Term |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac (Term_typeEs @ [conjE, bexE, TermE]) 1)),
     (rotate_tac 3 1),
     (asm_full_simp_tac (IFOL_ss addsimps Term_LAQ) 1),
     (REPEAT (dtac LAQ_D 1)),
     (eresolve_tac LAlpha_LTermEs2 1),
     (ALLGOALS bound_hyp_subst_tac),
     (ALLGOALS (eresolve_tac LBeta1_LTermEs)),
     (ALLGOALS bound_hyp_subst_tac),
     (ALLGOALS (REPEAT o (dtac LAQ_eqI))),
     (res_inst_tac [("B'", "LAQ(B')")] prem3 3),
     (res_inst_tac [("A'", "LAQ(A')")] prem2 2),
     (res_inst_tac [("x", "x"), ("N'", "LAQ(N')")] prem1 1),
     (safe_tac (ZF_cs addSIs [subst_type, LAQ_type]
              addSIs Term_intrs)),
     (TRYALL (etac LBeta1_type2)),
     (etac LFreeForInD2 1),
     (etac LFreeForInD3 1),
     (ALLGOALS (asm_full_simp_tac (LTerm_ss addsimps Term_LAQ
                                 addsimps [FV_LAQ, LBeta1_type2, 
                                           LFreeForInD3, LFreeForInD2,
                                           subst_LAQ]))),
     (ALLGOALS (REPEAT o ((ares_tac [bexI, LAQ_self, LAQ_I]) ORELSE'
                        (etac LBeta1_type2) ORELSE'
                        (etac LBeta1_type1) ORELSE'
                        (etac LAlpha_sym))))]);

qed_goalw "Beta1_substI" Lambda.thy [Beta1_def]
    "[| Beta1(M, M'); x: LVariable; N: Term |] ==> \
\        Beta1(subst(M, x, N), subst(M', x, N))"
  (fn [major, prem1, prem2] =>
    [(rtac (prem2 RS TermE) 1),
     (rtac ([major RS conjunct1, prem1] MRS Term_LFreeForInE) 1),
     (atac 1),
     (res_inst_tac [("n", "m")] 
    ([major RS conjunct2 RS conjunct1, prem1] MRS Term_LFreeForInE) 1),
     (atac 1),
     (cut_facts_tac [major RS conjunct2 RS conjunct2] 1),
     (REPEAT (etac bexE 1)),
     (asm_full_simp_tac (IFOL_ss addsimps [subst_LAQ]) 1),
     (REPEAT (ares_tac [LAQ_type, Lsubst_type, conjI] 1)),
     (dres_inst_tac [("X", "m")] 
      (Infinite_LVariable RS LBeta1_LAlpha_parallel) 1),
     (etac LFreeForInD2 1),
     (atac 1),
     (safe_tac (ZF_cs addSDs [LAQ_D])),
     (rtac (bexI RS bexI) 1),
     (etac LBeta1_LsubstI 1),
     (REPEAT (atac 1)),
     (REPEAT ((ares_tac [LAQ_I, LAlpha_LsubstI, LAlpha_refl] 1)
            ORELSE (etac LAlpha_trans 1)))]);

qed_goalw "Beta1_FV_lemma" Lambda.thy [Beta1_def]
    "Beta1(M, N) ==> FV(N) <= FV(M)"
  (fn [major] =>
    [(rtac (major RS conjunct1 RS TermE) 1),
     (rtac (major RS conjunct2 RS conjunct1 RS TermE) 1),
     (cut_facts_tac [major] 1),
     (REPEAT (eresolve_tac [bexE, conjE] 1)),
     (REPEAT (hyp_subst_tac 1)),
     (REPEAT (dtac (LAQ_D RS LAQ_eqI) 1)),
     (asm_full_simp_tac (IFOL_ss addsimps [FV_LAQ, LBeta1_type1, 
                                         LBeta1_type2]) 1),
     (etac LBeta1_LFV_lemma 1)]);


qed_goal "FV_subst_not_in_lemma" Lambda.thy
    "[| M: Term; x: LVariable; N: Term |] ==> \
\           x ~: FV(subst(M, x, N)) - FV(N)"
  (fn [prem1, prem2, prem3] =>
    [(cut_facts_tac [prem2] 1),
     (rtac (prem3 RS TermE) 1),
     (rtac ([prem1, prem2] MRS Term_LFreeForInE) 1),
     (atac 1),
     (asm_simp_tac (IFOL_ss addsimps [FV_LAQ, subst_LAQ]) 1),
     (rtac (FV_LAQ RS ssubst) 1),
     (safe_tac (ZF_cs addSIs [Lsubst_type] 
              addSEs [LFV_E, LFreeIn_LsubstE])),
     ((etac notE 1) THEN (etac LFV_I 1))]);

qed_goal "Beta1_LamE" Lambda.thy
    "[| Beta1(Lam(x, M), N); \
\       !!N'. [| x: LVariable; N = Lam(x, N'); Beta1(M, N')|] \
\          ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS Beta1_LamE1) 1),
     (forward_tac [Beta1_FV_lemma] 2),
     (cut_inst_tac [("M", "M"), ("x", "x"), ("N", "Var(y)")] 
    FV_subst_not_in_lemma 2),
     (asm_full_simp_tac (ZF_ss addsimps FV_eqns) 5),
     (etac disjE 5),
     (dres_inst_tac [("x", "y"), ("N", "Var(x)")] Beta1_substI 5),
     (REPEAT (ares_tac Term_intrs 2)),
     (forward_tac [Term_VarI] 2),
     (rotate_tac 9 2),
     (asm_full_simp_tac (IFOL_ss addsimps [subst_lemma2, subst_self]) 2),
     (rotate_tac 7 3),
     (asm_full_simp_tac (IFOL_ss addsimps [subst_self]) 3),
     (ALLGOALS (rtac prem)),
     (TRYALL atac),
     (safe_tac ZF_cs),
     (rtac Alpha 1),
     (fast_tac ZF_cs 4),
     (REPEAT (atac 1))]);

qed_goal "Fin_FV_I" Lambda.thy
    "M: Term ==> FV(M): Fin(LVariable)"
  (fn [major] =>
    [(rtac (major RS TermE) 1),
     (hyp_subst_tac 1),
     (asm_simp_tac (IFOL_ss addsimps [FV_LAQ]) 1),
     (etac LFV_Fin 1)]);

qed_goal "Infinite_LVariable_Alpha_lemma2" Lambda.thy
    "[| M: Term; x: LVariable; X: Fin(LVariable) |]==> \
\       EX y: LVariable. EX M': Term. Lam(x, M) = Lam(y, M') & y ~: X"
  (fn [major, prem1, prem2] =>
    [(res_inst_tac [("F", "X Un FV(M)")] 
    (Infinite_LVariable RS InfiniteE) 1),
     (REPEAT (ares_tac [Fin_UnI, Fin_FV_I, prem2, major, bexI, conjI] 1)),
     (rtac Alpha 1),
     (atac 2),
     (fast_tac ZF_cs 3),
     (fast_tac ZF_cs 3),
     (REPEAT (ares_tac ([major, prem1, subst_type] @ Term_intrs) 1))]);

qed_goal "Beta1_AppE" Lambda.thy
    "[| Beta1(App(A, B), N); \
\       !!x N'. [| x: LVariable; N': Term; B: Term; x ~: FV(B); \
\          A = Lam(x, N'); N = subst(N', x, B) |] ==> R; \
\       !!A'. [| B: Term; Beta1(A, A'); N = App(A', B) |] ==> R; \
\       !!B'. [| A: Term; Beta1(B, B'); N = App(A, B') |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (major RS Beta1_AppE1) 1),
     (cut_inst_tac [("M", "N'"), ("X", "cons(x, FV(B))")] 
      Infinite_LVariable_Alpha_lemma2 1),
     (REPEAT (ares_tac ([Fin_FV_I] @ Fin.intrs) 1)),
     (REPEAT (eresolve_tac (Term_typeEs @ [conjE, bexE]) 1)),
     (subgoal_tac "y ~= x" 1),
     (fast_tac ZF_cs 2),
     (swap_res_tac [consI2] 1),
     (etac swap 1),
     (etac swap 1),
     (rotate_tac 7 1),
     (asm_full_simp_tac IFOL_ss 1),
     (rtac prem1 1),
     (atac 5),
     (REPEAT (atac 1)),
     (rotate_tac 1 1),
     (asm_full_simp_tac (ZF_ss addsimps Term_free_iffs) 1),
     (SELECT_GOAL (safe_tac ZF_cs) 1),
     (asm_simp_tac (IFOL_ss addsimps [subst_lemma2]) 1),
     (rtac prem2 1),
     (rtac prem3 4),
     (REPEAT (atac 1))]);

val Beta1_TermEs = [Beta1_VarE, Beta1_LamE, Beta1_AppE];
