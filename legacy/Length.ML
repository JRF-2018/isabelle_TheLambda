(*
    File:        Length.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open Length;

val LLength_eqns = map (fn s => prove_goalw Length.thy
                     [LLength_def] s
                     (fn prems => 
                      [simp_tac (ZF_ss addsimps LTerm_rec_eqns) 1]))
    ["LLength(LVar(x)) = 0",
     "LLength(LLam(x, M)) = succ(LLength(M))",
     "LLength(LApp(M, N)) = succ(LLength(M) Un LLength(N))"];

qed_goal "LLength_type" Length.thy
    "M: LTerm ==> LLength(M): nat"
  (fn [major] =>
    [(LTermOcc.ind_tac "M" [major] 1),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps LLength_eqns))),
     (REPEAT (ares_tac [nat_succI, nat_UnI, nat_0I] 1))]);

qed_goal "LSkeltonEq_imp_LLength_eq" Length.thy
    "LSkeltonEq(M, N) ==> LLength(M) = LLength(N)"
  (fn [major] =>
    [(rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "N")] spec 1),
     (LTermOcc.ind_tac "M" [major RS LSkeltonEqD1] 1),
     (safe_tac (ZF_cs addSEs LSkeltonEq_LTermEs)),
     (ALLGOALS (asm_full_simp_tac (LTerm_ss addsimps LLength_eqns)))]);

qed_goalw "Length_LAQ" Length.thy [Length_def]
    "m: LTerm ==> Length(LAQ(m)) = LLength(m)"
  (fn [major] =>
    [(cut_facts_tac [major] 1),
     (rtac the_equality 1),
     (rtac INT_I 1),
     (etac LAQ_self 2),
     (dtac LAQ_D 1),
     (dtac (LAlphaD1 RS LSkeltonEq_imp_LLength_eq) 1),
     (fast_tac ZF_cs 1),
     (dtac INT_E 1),
     (etac LAQ_self 1),
     (etac singletonE 1),
     (atac 1)]);

qed_goal "Length_type" Length.thy
    "M: Term ==> Length(M): nat"
  (fn [major] =>
    [(rtac (major RS TermE) 1),
     (hyp_subst_tac 1),
     (asm_simp_tac (IFOL_ss addsimps [Length_LAQ]) 1),
     (etac LLength_type 1)]);

qed_goal "Length_Var" Length.thy
    "x: LVariable ==> Length(Var(x)) = 0"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ addsimps [Length_LAQ]
                  addsimps LLength_eqns) 1)]);

qed_goal "Length_Lam" Length.thy
    "[| x: LVariable; M: Term |] ==> \
\         Length(Lam(x, M)) = succ(Length(M))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac TermE 1)),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ addsimps [Length_LAQ]
                  addsimps LLength_eqns) 1)]);

qed_goal "Length_App" Length.thy
    "[| M: Term; N: Term |] ==> \
\         Length(App(M, N)) = succ(Length(M) Un Length(N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac TermE 1)),
     (asm_simp_tac (LTerm_ss addsimps Term_LAQ addsimps [Length_LAQ]
                  addsimps LLength_eqns) 1)]);

val Length_eqns = [Length_Var, Length_Lam, Length_App];


qed_goal "Length_induct" Length.thy
    "[| M: Term; \
\       !!M. [| M: Term; ALL N: Term. Length(N) < Length(M) --> P(N) |] \
\            ==> P(M) \
\    |] ==> P(M)"
  (fn [major, prem] =>
    [(rtac (major RS rev_mp) 1),
     (res_inst_tac [("P", "?n = Length(M)")] rev_mp 1),
     (rtac (major RSN (2, bspec)) 2),
     (res_inst_tac [("P", 
                     "%n. ALL M: Term. n = Length(M) --> M: Term --> P(M)")]
                   (major RS Length_type RS complete_induct) 2),
     (rtac refl 1),
     (safe_tac ZF_cs),
     (etac prem 1),
     (safe_tac ZF_cs),
     (etac (bspec RS bspec RS mp RS mp) 1),
     (etac ltD 1),
     (REPEAT (ares_tac [refl] 1))]);

qed_goal "Term_induct2" Length.thy
    "[| M: Term; X: Fin(LVariable); \
\       !! x . x: LVariable ==> P(Var(x)); \
\       !! x M . [| x: LVariable; x ~: X; M: Term; P(M) |] \
\           ==> P(Lam(x, M)); \
\       !! M N . [| M: Term; P(M); N: Term; P(N) |] ==> P(App(M, N)) \
\    |] ==> P(M)"
  (fn major::prem1::prems =>
    [(rtac (major RS Length_induct) 1),
     (etac Term_elim 1),
     (ALLGOALS hyp_subst_tac),
     (rtac (prem1 RSN (3, Infinite_LVariable_Alpha_lemma2) RS bexE) 2),
     (REPEAT (atac 2)),
     (REPEAT (eresolve_tac [bexE, conjE] 2)),
     (ALLGOALS (rotate_tac 1)),
     (asm_full_simp_tac IFOL_ss 2),
     (ALLGOALS (asm_full_simp_tac (ZF_ss addsimps Length_eqns))),
     (ALLGOALS (resolve_tac prems)),
     (TRYALL atac),
     (ALLGOALS (etac (bspec RS mp))),
     (REPEAT (ares_tac [nat_into_Ord, le_refl, Length_type, 
                      Un_upper1_le, Un_upper2_le] 1))]);


val Term_typechecks = Term_intrs 
    @ [subst_type, Length_type]
    @ nth_typechecks;

val Term_simps = Term_free_iffs @ Length_eqns @ subst_eqns @ FV_eqns;

val Term_ss = nth_ss addsimps Term_simps 
    setsolver (type_auto_tac Term_typechecks);
