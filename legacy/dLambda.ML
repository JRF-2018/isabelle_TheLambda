(*
    File:        dLambda.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open dLambda;

val dOcc_domain = dTermOcc.use_thm Occ_ind_cond_Occ_domain;
val dOcc_in_Occ_range = dTermOcc.use_thm Occ_ind_cond_Occ_in_Occ_range;

qed_goal "dOcc_typeD1" dLambda.thy
    "[| <l, T>: dOcc(M); M: dTerm |] ==> l: list(nat)"
  (fn [major,prem] =>
    [(rtac (major RS (prem RS dOcc_domain RS subsetD RS SigmaD1)) 1)]);

qed_goal "dOcc_typeD2" dLambda.thy
    "[| <l, T>: dOcc(M); M: dTerm |] ==> T: dTag"
  (fn [major,prem] =>
    [(rtac (major RS (prem RS dOcc_domain RS subsetD RS SigmaD2)) 1)]);

val dTerm_typeEs = map (fn s => prove_goal dLambda.thy s
                        (fn [major, prem] =>
                         [(rtac (major RS dTerm.elim) 1),
                          (ALLGOALS (fast_tac (ZF_cs addSEs dTerm.free_SEs 
                                               addIs [prem])))]))
    ["[| dVar(x): dTerm; x: LVariable ==> R |] ==> R",
     "[| dBound(n): dTerm; n: nat ==> R |] ==> R",
     "[| dLam(M): dTerm; M: dTerm ==> R |] ==> R",
     "[| dApp(M, N): dTerm; [| M: dTerm; N: dTerm |] ==> R |] ==> R"];

val dTag_typeEs = map (fn s => prove_goal dLambda.thy s
                        (fn [major, prem] =>
                         [(rtac (major RS dTermOcc.Tag.elim) 1),
                          (ALLGOALS (fast_tac (ZF_cs addSEs 
                                               dTermOcc.Tag.free_SEs 
                                               addIs [prem])))]))
    ["[| TdVar(x): dTag; x: LVariable ==> R |] ==> R",
     "[| TdBound(n): dTag; n: nat ==> R |] ==> R"];


val dTag_simps = map dTermOcc.Tag.mk_free
    ["TdVar(x) = TdVar(y) <-> x = y",
     "TdBound(n) = TdBound(m) <-> n = m"];

qed_goal "dOcc_dVarE" dLambda.thy
    "[| u: dOcc(dVar(x)); \
\       u = <[], TdVar(x)> ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps dTermOcc.Occ_eqns) 1),
     (etac Occ_consE 1),
     (etac prem 1),
     (asm_full_simp_tac (IFOL_ss addsimps [length_Nil]) 1),
     (etac emptyE 1)]);

qed_goal "dOcc_dBoundE" dLambda.thy
    "[| u: dOcc(dBound(n)); \
\       u = <[], TdBound(n)> ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps dTermOcc.Occ_eqns) 1),
     (etac Occ_consE 1),
     (etac prem 1),
     (asm_full_simp_tac (IFOL_ss addsimps [length_Nil]) 1),
     (etac emptyE 1)]);

qed_goal "dOcc_dLamE" dLambda.thy
    "[| u: dOcc(dLam(M)); \
\       u = <[], TdLam> ==> R; \
\       !! l T. [| u = <Cons(0, l), T>; <l, T>: dOcc(M) |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2] =>
    [(cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps dTermOcc.Occ_eqns) 1),
     (etac Occ_consE 1),
     (etac prem1 1),
     (asm_full_simp_tac list_ss 1),
     (etac succE 1),
     (etac emptyE 2),
     (rtac prem2 1),
     (ALLGOALS (REPEAT o hyp_subst_tac)),
     (asm_full_simp_tac nth_ss 2),
     (rtac refl 1)]);

qed_goal "dOcc_dAppE" dLambda.thy
    "[| u: dOcc(dApp(M, N)); \
\       u = <[], TdApp> ==> R; \
\       !! l T. [| u = <Cons(0, l), T>; <l, T>: dOcc(M) |] ==> R; \
\       !! l T. [| u = <Cons(1, l), T>; <l, T>: dOcc(N) |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps dTermOcc.Occ_eqns) 1),
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

val dOcc_dTermEs = [dOcc_dVarE, dOcc_dBoundE, dOcc_dLamE, dOcc_dAppE];

val dOcc_dTermIs = map (fn s => prove_goal dLambda.thy s
                         (fn prems =>
                          [(cut_facts_tac prems 1),
                           (asm_simp_tac 
                            (IFOL_ss addsimps dTermOcc.Occ_eqns) 1),
                           (resolve_tac [Occ_consI2, Occ_consI1] 1),
                           (IF_UNSOLVED (ALLGOALS (asm_simp_tac nth_ss))),
                           (IF_UNSOLVED (REPEAT 
                                         (ares_tac [succI1, succI2] 1)))]))
    ["<[], TdVar(x)>: dOcc(dVar(x))",
     "<[], TdBound(n)>: dOcc(dBound(n))",
     "<[], TdLam>: dOcc(dLam(M))",
     "<l, T>: dOcc(M) ==> <Cons(0, l), T>: dOcc(dLam(M))",
     "<[], TdApp>: dOcc(dApp(M, N))",
     "<l, T>: dOcc(M) ==> <Cons(0, l), T>: dOcc(dApp(M, N))",
     "<l, T>: dOcc(N) ==> <Cons(1, l), T>: dOcc(dApp(M, N))"];

val dsubterm_eqns = [dTermOcc.use_thm def_subterm_Nil] @
    (map (fn s => prove_goal dLambda.thy s
          (fn prems =>
           [(cut_facts_tac prems 1),
            (asm_simp_tac (dTermOcc.Term_cons_ss addsimps 
                           [dTermOcc.use_thm def_subterm_Cons]) 1)]))
     ["[| M: dTerm; l: list(nat) |] ==> \
      \       dsubterm(dLam(M), Cons(0, l)) = dsubterm(M, l)",
      "[| A: dTerm; B: dTerm; l: list(nat) |] ==> \
       \       dsubterm(dApp(A, B), Cons(0, l)) = dsubterm(A, l)",
      "[| A: dTerm; B: dTerm; l: list(nat) |] ==> \
       \       dsubterm(dApp(A, B), Cons(1, l)) = dsubterm(B, l)"]);

val dAbst_eqns = map (fn s => prove_goalw dLambda.thy [dAbst_def] s
    (fn prems => 
     [(asm_simp_tac (ZF_ss addsimps (prems@dTermOcc.rec_eqns)) 1)]))
    ["n: nat ==> dAbst(dVar(y), x, n) = if(x = y, dBound(n), dVar(y))",
     "n: nat ==> dAbst(dBound(i), x, n) = dBound(i)",
     "n: nat ==> dAbst(dLam(M), x, n) = dLam(dAbst(M, x, succ(n)))",
     "n: nat ==> dAbst(dApp(A, B), x, n) = \
\                   dApp(dAbst(A, x, n), dAbst(B, x, n))"];

qed_goal "dAbst_type" dLambda.thy
    "[| M: dTerm; n: nat |] ==> dAbst(M, x, n): dTerm"
  (fn [major, sub] =>
    [(rtac (sub RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major] 1),
     (ALLGOALS (asm_simp_tac (ZF_ss addsimps dAbst_eqns))),
     (rtac ballI 3),
     (dtac bspec 3),
     (etac nat_succI 3),
     (ALLGOALS (fast_tac (ZF_cs addIs dTerm.intrs addIs [if_type])))]);

val dLift_eqns = map (fn s => prove_goalw dLambda.thy [dLift_def] s
    (fn prems => 
     [(asm_simp_tac (ZF_ss addsimps (prems@dTermOcc.rec_eqns)) 1)]))
    ["n: nat ==> dLift(dVar(x), n) = dVar(x)",
     "n: nat ==> dLift(dBound(i), n) = if (i < n, dBound(i), dBound(succ(i)))",
     "n: nat ==> dLift(dLam(M), n) = dLam(dLift(M, succ(n)))",
     "n: nat ==> dLift(dApp(A, B), n) = \
\                   dApp(dLift(A, n), dLift(B, n))"];

qed_goal "dLift_type" dLambda.thy
    "[| M: dTerm; n: nat |] ==> dLift(M, n): dTerm"
  (fn [major, sub] =>
    [(rtac (sub RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major] 1),
     (ALLGOALS (asm_simp_tac (ZF_ss addsimps dLift_eqns))),
     (rtac ballI 3),
     (dtac bspec 3),
     (etac nat_succI 3),
     (ALLGOALS 
      (fast_tac (ZF_cs addSIs dTerm.intrs addSIs [if_type, nat_succI])))]);

val dSubst_eqns = map (fn s => prove_goalw dLambda.thy [dSubst_def] s
    (fn prems => 
     [(asm_simp_tac (ZF_ss addsimps (prems@dTermOcc.rec_eqns)) 1)]))
    ["[| n: nat; N: dTerm |] ==> dSubst(dVar(x), n, N) = dVar(x)",
     "[| n: nat; N: dTerm |] ==> dSubst(dBound(i), n, N) = \
\                 if (n < i, dBound(i #- 1), if (n = i, N, dBound(i)))",
     "[| n: nat; N: dTerm |] ==> dSubst(dLam(M), n, N) \
\                                   = dLam(dSubst(M, succ(n), dLift(N, 0)))",
     "[| n: nat; N: dTerm |] ==> dSubst(dApp(A, B), n, N) = \
\                   dApp(dSubst(A, n, N), dSubst(B, n, N))"];

qed_goal "dSubst_type" dLambda.thy
    "[| M: dTerm; n: nat; N: dTerm |] ==> dSubst(M, n, N): dTerm"
  (fn [major, sub, prem] =>
    [(rtac (sub RSN (2, bspec)) 1),
     (rtac (prem RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major] 1),
     (ALLGOALS (asm_simp_tac (ZF_ss addsimps dSubst_eqns))),
     (safe_tac (ZF_cs addSIs dTerm.intrs 
                addSIs [if_type, diff_type, nat_1I])),
     (ALLGOALS (etac (bspec RS bspec))),
     (REPEAT (ares_tac [dLift_type, nat_succI, nat_0I] 1))]);

val dDeg_eqns = map (fn s => prove_goalw dLambda.thy [dDeg_def] s
    (fn prems => 
     [(asm_simp_tac (ZF_ss addsimps (prems@dTermOcc.rec_eqns)) 1)]))
    ["dDeg(dVar(x)) = 0",
     "dDeg(dBound(i)) = succ(i)",
     "dDeg(dLam(M)) = dDeg(M) #- 1",
     "dDeg(dApp(A, B)) = dDeg(A) Un dDeg(B)"];

qed_goalw "dDeg_type" dLambda.thy [dDeg_def]
    "M: dTerm ==> dDeg(M): nat"
  (fn prems =>
    [(rtac dTermOcc.rec_type 1),
     (resolve_tac prems 1),
     (REPEAT (ares_tac [diff_type, nat_UnI, nat_succI, nat_0I] 1))]);


(** dLamDeg **)
qed_goalw "dLamDegBase_Nil" dLambda.thy [dLamDegBase_def]
    "M: dTerm ==> dLamDegBase([], M) = 0"
  (fn [major] =>
    [(safe_tac (eq_cs addSEs [initseg_NilE]))]);

qed_goalw "dLamDegBase_Cons_dLam" dLambda.thy [dLamDegBase_def]
    "l: list(nat) ==> dLamDegBase(Cons(0, l), dLam(M)) \
\                  = cons(<[], TdLam>, Occ_shift(0, dLamDegBase(l, M)))"
  (fn [major] =>
    [(rtac equalityI 1),
     (safe_tac (ZF_cs addSEs list.free_SEs
              addSEs [Occ_shiftE, initseg_ConsE] addSEs dOcc_dTermEs)),
     (swap_res_tac [Occ_shiftI] 1),
     (fast_tac ZF_cs 1),
     (resolve_tac dOcc_dTermIs 1),
     (eresolve_tac dOcc_dTermIs 2),
     (ALLGOALS (REPEAT o (ares_tac [conjI, refl, exI]))),
     (fast_tac (ZF_cs addSEs list.free_SEs) 1),
     (fast_tac (ZF_cs addSEs list.free_SEs) 2),
     (REPEAT (ares_tac (list.intrs @ [major, initseg_NilI, initseg_ConsI,
                                    nat_0I]) 1))]);

qed_goalw "dLamDegBase_Cons_dApp1" dLambda.thy [dLamDegBase_def]
    "l: list(nat) ==> dLamDegBase(Cons(0, l), dApp(M, N)) \
\                  = Occ_shift(0, dLamDegBase(l, M))"
  (fn [major] =>
    [(rtac equalityI 1),
     (safe_tac (ZF_cs addSEs list.free_SEs addSEs dTermOcc.Tag.free_SEs
              addSEs [Occ_shiftE, initseg_ConsE] addSEs dOcc_dTermEs)),
     (rtac Occ_shiftI 1),
     (fast_tac ZF_cs 1),
     (eresolve_tac dOcc_dTermIs 1),
     (REPEAT (ares_tac [conjI, refl, exI] 1)),
     (fast_tac (ZF_cs addSEs list.free_SEs) 1),
     (REPEAT (ares_tac (list.intrs @ [major, initseg_ConsI, nat_0I]) 1))]);

qed_goalw "dLamDegBase_Cons_dApp2" dLambda.thy [dLamDegBase_def]
    "l: list(nat) ==> dLamDegBase(Cons(1, l), dApp(M, N)) \
\                  = Occ_shift(1, dLamDegBase(l, N))"
  (fn [major] =>
    [(rtac equalityI 1),
     (safe_tac (ZF_cs addSEs list.free_SEs addSEs dTermOcc.Tag.free_SEs
              addSEs [Occ_shiftE, initseg_ConsE] addSEs dOcc_dTermEs)),
     (rtac Occ_shiftI 1),
     (fast_tac ZF_cs 1),
     (eresolve_tac dOcc_dTermIs 1),
     (REPEAT (ares_tac [conjI, refl, exI] 1)),
     (fast_tac (ZF_cs addSEs list.free_SEs) 1),
     (REPEAT (ares_tac (list.intrs @ [major, initseg_ConsI, nat_1I]) 1))]);

qed_goalw "dLamDeg_type" dLambda.thy [dLamDeg_def, dLamDegBase_def]
    "M: dTerm ==> dLamDeg(l, M): nat"
  (fn [major] =>
    [(REPEAT (ares_tac [Finite_imp_card_nat, Fin_imp_Finite,
                      dTermOcc.use_thm Occ_ind_cond_Occ_FinI,
                      Collect_subset, major, Fin_subset] 1))]);

qed_goalw "dLamDeg_Nil" dLambda.thy [dLamDeg_def]
    "M: dTerm ==> dLamDeg([], M) = 0"
  (fn [major] =>
    [(asm_simp_tac (IFOL_ss addsimps [major RS dLamDegBase_Nil]) 1),
     (rtac (Card_0 RS Card_cardinal_eq) 1)]);

qed_goalw "dLamDeg_Cons_dLam" dLambda.thy [dLamDeg_def]
    "[| M: dTerm; l: list(nat) |]  ==> \
\          dLamDeg(Cons(0, l), dLam(M)) = succ(dLamDeg(l, M))"
  (fn [major, prem] =>
    [(simp_tac (IFOL_ss addsimps [prem RS dLamDegBase_Cons_dLam]) 1),
     (rtac trans 1),
     (rtac Finite_cardinal_cons 1),
     (res_inst_tac [("f", "succ")] function_apply_eq 3),
     (rtac Occ_shift_cardinal 3),
     (rewrite_goals_tac [dLamDegBase_def]),
     (REPEAT (ares_tac [Fin_imp_Finite, Occ_shift_FinI, 
                      Collect_subset, major, nat_0I,
                      dTermOcc.use_thm Occ_ind_cond_Occ_FinI, 
                      Fin_subset] 1)),
     (fast_tac (ZF_cs addSEs list.free_SEs addSEs [Occ_shiftE]) 1),
     (rtac subset_trans 1),
     (REPEAT (ares_tac [major, dOcc_domain, Collect_subset] 1))]);

qed_goalw "dLamDeg_Cons_dApp1" dLambda.thy [dLamDeg_def]
    "[| M: dTerm; l: list(nat) |]  ==> \
\          dLamDeg(Cons(0, l), dApp(M, N)) = dLamDeg(l, M)"
  (fn [major, prem] =>
    [(simp_tac (IFOL_ss addsimps [prem RS dLamDegBase_Cons_dApp1]) 1),
     (rtac Occ_shift_cardinal 1),
     (rewrite_goals_tac [dLamDegBase_def]),
     (rtac subset_trans 1),
     (REPEAT (ares_tac [major, dOcc_domain, Collect_subset] 1))]);

qed_goalw "dLamDeg_Cons_dApp2" dLambda.thy [dLamDeg_def]
    "[| N: dTerm; l: list(nat) |]  ==> \
\          dLamDeg(Cons(1, l), dApp(M, N)) = dLamDeg(l, N)"
  (fn [major, prem] =>
    [(simp_tac (IFOL_ss addsimps [prem RS dLamDegBase_Cons_dApp2]) 1),
     (rtac Occ_shift_cardinal 1),
     (rewrite_goals_tac [dLamDegBase_def]),
     (rtac subset_trans 1),
     (REPEAT (ares_tac [major, dOcc_domain, Collect_subset] 1))]);

val dLamDeg_eqns = [dLamDeg_Nil, dLamDeg_Cons_dLam, dLamDeg_Cons_dApp1,
                    dLamDeg_Cons_dApp2];

(** dFV **)

qed_goalw "dFV_I" dLambda.thy [dFV_def]
    "[| <l, TdVar(x)>: dOcc(M); M: dTerm |] ==> x: dFV(M)"
  (fn [major, prem] =>
    [(cut_facts_tac [[major, prem] MRS dOcc_typeD2] 1),
     (eresolve_tac dTag_typeEs 1),
     (REPEAT (ares_tac [exI, CollectI, major] 1))]);

qed_goalw "dFV_I2" dLambda.thy [dFV_def]
    "[| <l, TdVar(x)>: dOcc(M); x: LVariable |] ==> x: dFV(M)"
  (fn [major, prem] =>
    [(cut_facts_tac [prem] 1),
     (REPEAT (ares_tac [exI, CollectI, major] 1))]);

qed_goalw "dFV_E" dLambda.thy [dFV_def]
    "[| x: dFV(M); !!l. [| x: LVariable; <l, TdVar(x)>: dOcc(M) |] ==> R |] \
\     ==> R"
  (fn [major, prem] =>
    [(rtac (major RS CollectE) 1),
     (etac exE 1),
     (REPEAT (ares_tac [prem] 1))]);

qed_goalw "dFV_Fin" dLambda.thy [dFV_def]
    "M: dTerm ==> dFV(M): Fin(LVariable)"
  (fn [prem] =>
    [(rtac (prem RS (dTermOcc.use_thm Occ_ind_cond_Occ_FinI) RS Fin_induct) 1),
     (simp_tac ZF_ss 1),
     (resolve_tac Fin.intrs 1),
     (etac SigmaE 1),
     (etac dTermOcc.Tag.elim 1),
     (ALLGOALS (REPEAT o hyp_subst_tac)),
     (res_inst_tac [("P", "%x. x: ?X")] ssubst 1),
     (eresolve_tac Fin.intrs 2),
     (atac 2),
     (res_inst_tac [("P", "%x. x: ?X")] ssubst 2),
     (atac 3),
     (res_inst_tac [("P", "%x. x: ?X")] ssubst 3),
     (atac 4),
     (res_inst_tac [("P", "%x. x: ?X")] ssubst 4),
     (atac 5),
     (ALLGOALS (rtac equalityI)),
     (TRYALL (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs)))]);

qed_goal "dFV_not_in_lemma" dLambda.thy
    "[| x ~: dFV(M); M: dTerm |] ==> ~(EX l. <l, TdVar(x)>: dOcc(M))"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (fast_tac (ZF_cs addIs [dFV_I, prem]) 1)]);


qed_goal "dFV_dVar" dLambda.thy
    "x: LVariable ==> dFV(dVar(x)) = {x}"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs [dFV_E]
              addSEs dTermOcc.Tag.free_SEs)),
     (REPEAT (ares_tac ([dFV_I] @ dTerm.intrs @ dOcc_dTermIs) 1))]);

qed_goal "dFV_dBound" dLambda.thy
    "dFV(dBound(x)) = 0"
  (fn prems =>
    [(rtac equalityI 1),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs [dFV_E]
              addSEs dTermOcc.Tag.free_SEs))]);

qed_goal "dFV_dLam" dLambda.thy
    "M: dTerm ==> dFV(dLam(M)) = dFV(M)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs [dFV_E]
              addSEs dTermOcc.Tag.free_SEs)),
     (REPEAT (ares_tac ([dFV_I] @ dTerm.intrs @ dOcc_dTermIs) 1))]);

qed_goal "dFV_dApp" dLambda.thy
    "[| M: dTerm; N: dTerm |] ==> dFV(dApp(M, N)) = dFV(M) Un dFV(N)"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs [dFV_E]
              addSEs dTermOcc.Tag.free_SEs)),
     (etac swap 2),
     (REPEAT ((ares_tac ([dFV_I] @ dTerm.intrs) 1)
            ORELSE (eresolve_tac dOcc_dTermIs 1)))]);

val dFV_eqns = [dFV_dVar, dFV_dBound, dFV_dApp, dFV_dLam];

val dTerm_ss = nth_ss 
    delsimps [nat_ltI]
    addsimps [nat_succ_Un, Un_diff]
    addsimps dArity_eqns
    addsimps [add_0_right, add_succ_right, gt_not_eq, lt_asym_if,
              le_asym_if, not_lt_iff_le, lt_irrefl_if, 
              diff_le_iff, lt_diff_iff, diff_diff_eq_diff_add, 
              [nat_into_Ord, nat_into_Ord] MRS Un_least_lt_iff]
    addsimps dLift_eqns addsimps dSubst_eqns
    addsimps dsubterm_eqns addsimps dDeg_eqns
    addsimps dAbst_eqns addsimps dLamDeg_eqns addsimps dFV_eqns
    setsolver (type_auto_tac (dTerm.intrs @ dTerm_Term_cons_typechecks @
                              [dDeg_type, dAbst_type, diff_type,
                               dSubst_type, dLift_type,
                               dLamDeg_type, nat_UnI]));

(** dProp **)
qed_goalw "dPropI" dLambda.thy [dProp_def]
    "[| M: dTerm; dDeg(M) = 0 |] ==> M: dProp"
  (fn prems =>
    [(fast_tac (ZF_cs addIs prems) 1)]);

qed_goalw "dPropE" dLambda.thy [dProp_def]
    "[| M: dProp; [| M: dTerm; dDeg(M) = 0 |] ==> R |] ==> R"
  (fn major::prems =>
    [(rtac (major RS CollectE) 1),
     (REPEAT (ares_tac prems 1))]);

qed_goalw "dPropD1" dLambda.thy [dProp_def]
    "M: dProp ==> M: dTerm"
  (fn [prem] =>
    [(rtac (prem RS CollectD1) 1)]);

qed_goalw "dPropD2" dLambda.thy [dProp_def]
    "M: dProp ==> dDeg(M) = 0"
  (fn [prem] =>
    [(rtac (prem RS CollectD2) 1)]);

qed_goal "dProp_dVarI" dLambda.thy
    "x: LVariable ==> dVar(x): dProp"
  (fn prems =>
    [(fast_tac (ZF_cs addIs [dPropI] addIs prems addIs dTerm.intrs 
              addIs dDeg_eqns) 1)]);

qed_goal "dProp_dLamI1" dLambda.thy
    "M: dProp ==> dLam(M): dProp"
  (fn [prem] =>
    [(rtac (prem RS dPropE) 1),
     (rtac dPropI 1),
     (asm_simp_tac (arith_ss addsimps dDeg_eqns) 2),
     (REPEAT (ares_tac dTerm.intrs 1))]);

qed_goal "dProp_dLamI2" dLambda.thy
    "[| M: dTerm; dDeg(M) = 1 |] ==> dLam(M): dProp"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac dPropI 1),
     (asm_simp_tac (arith_ss addsimps dDeg_eqns) 2),
     (REPEAT (ares_tac dTerm.intrs 1))]);

qed_goal "dProp_dAppI" dLambda.thy
    "[| A: dProp; B: dProp |] ==> dApp(A, B): dProp"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (REPEAT (etac dPropE 1)),
     (rtac dPropI 1),
     (asm_simp_tac (arith_ss addsimps dDeg_eqns) 2),
     (REPEAT (ares_tac dTerm.intrs 1))]);

val dProp_dTermIs = [dProp_dVarI, dProp_dLamI1, dProp_dLamI2, dProp_dAppI];

qed_goal "dProp_dVarE" dLambda.thy
    "[| dVar(x): dProp; x: LVariable ==> R |] ==> R"
  (fn major::prems =>
    [(rtac (major RS dPropE) 1),
     (eresolve_tac dTerm_typeEs 1),
     (eresolve_tac prems 1)]);

qed_goal "dProp_dBoundE" dLambda.thy
    "dBound(n): dProp ==> R"
  (fn major::prems =>
    [(rtac (major RS dPropE) 1),
     (asm_full_simp_tac (IFOL_ss addsimps dDeg_eqns) 1),
     (etac succ_neq_0 1)]);

qed_goal "dProp_dLamE" dLambda.thy
    "[| dLam(M): dProp; \
\       M: dProp ==> R; \
\       [| M: dTerm; dDeg(M) = 1 |] ==> R \
\    |] ==> R"
  (fn major::prems =>
    [(rtac (major RS dPropE) 1),
     (asm_full_simp_tac (IFOL_ss addsimps dDeg_eqns) 1),
     (eresolve_tac dTerm_typeEs 1),
     (rtac (dDeg_type RS natE) 1),
     (atac 1),
     (rotate_tac 1 2),
     (asm_full_simp_tac arith_ss 2),
     (ALLGOALS (fast_tac (ZF_cs addIs [dPropI] addIs prems)))]);

qed_goal "dProp_dAppE" dLambda.thy
    "[| dApp(A, B): dProp; [| A: dProp; B: dProp |] ==> R |] ==> R"
  (fn major::prems =>
    [(rtac (major RS dPropE) 1),
     (asm_full_simp_tac (IFOL_ss addsimps dDeg_eqns) 1),
     (eresolve_tac dTerm_typeEs 1),
     (resolve_tac prems 1),
     (ALLGOALS (rtac dPropI)),
     (TRYALL atac),
     (ALLGOALS ((rtac equals0I) THEN' (dtac equals0D))),
     (etac UnI2 3),
     (etac UnI1 1),
     (REPEAT (atac 1))]);

val dProp_dTermEs = [dProp_dVarE, dProp_dBoundE, dProp_dLamE, dProp_dAppE];

qed_goal "dProp_induct" dLambda.thy
    "[| M: dProp; \
\       !! x. x: LVariable ==> P(dVar(x)); \
\       !! M. [| M: dProp; P(M) |] ==> P(dLam(M)); \
\       !! M. [| M: dTerm; dDeg(M) = 1 |] ==> P(dLam(M)); \
\       !! A B. [| A: dProp; P(A); B: dProp; P(B) |] ==> P(dApp(A, B)) \
\    |] ==> P(M)"
  (fn [major, prem1, prem2, prem3, prem4] =>
    [(rtac (major RS dPropD2 RS rev_mp) 1),
     (dTermOcc.ind_tac "M" [major RS dPropD1] 1),
     (ALLGOALS ((rtac impI) THEN' (asm_full_simp_tac dTerm_ss))),
     (dtac diff_eq_0D 3),
     (etac FalseE 2),
     (etac prem1 1),
     (REPEAT (ares_tac [dDeg_type, nat_1I] 1)),
     (dtac (le_succ_iff RS iffD1) 1),
     (etac disjE 1),
     (dtac (le0_iff RS iffD1) 1),
     (subgoals_tac ["dDeg(M) = 0", "dDeg(N) = 0"] 3),
     (REPEAT ((rtac equals0I 4) THEN (etac equals0D 4) 
            THEN (eresolve_tac [UnI1, UnI2] 4))),
     (rtac prem4 3),
     (rtac prem3 2),
     (rtac prem2 1),
     (TRYALL (rtac dPropI)),
     (safe_tac ZF_cs)]);

(** dBoundBy **)
qed_goalw "dBoundByI" dLambda.thy [dBoundBy_def]
    "[| M: dTerm; <m, TdBound(n)>: dOcc(M); <l, TdLam>: dOcc(M); \
\       m = l @ x; dLamDeg(x, dsubterm(M, l)) = succ(n) \
\    |] ==> dBoundBy(<m, TdBound(n)>, <l, TdLam>, M)"
  (fn prems =>
    [(fast_tac (ZF_cs addIs prems) 1)]);

qed_goalw "dBoundByE" dLambda.thy [dBoundBy_def]
    "[| dBoundBy(u, v, M); \
\       !! l n x. [| u = <l @ x, TdBound(n)>; v = <l, TdLam>; \
\         M: dTerm; l: list(nat); x: list(nat); \
\         <l @ x, TdBound(n)>: dOcc(M); <l, TdLam>: dOcc(M); \
\         dLamDeg(x, dsubterm(M, l)) = succ(n) \
\       |] ==> R \
\    |] ==> R"
  (fn [major,prem] =>
    [(rtac (major RS conjE) 1),
     (REPEAT (eresolve_tac [conjE, exE] 1)),
     (rtac prem 1),
     (ALLGOALS hyp_subst_tac),
     (REPEAT (ares_tac [refl] 1)),
     ((dtac dOcc_typeD1 2) THEN (etac app_typeD 3)),
     (REPEAT ((etac dOcc_typeD1 1) ORELSE (ares_tac [refl] 1)))]);

qed_goalw "dBoundByD1" dLambda.thy [dBoundBy_def]
    "dBoundBy(u, v, M) ==> M: dTerm"
  (fn [major] =>
    [(rtac (major RS conjunct1) 1)]);

qed_goal "dBoundBy_dLamI1" dLambda.thy
    "[| M: dTerm; dLamDeg(m, M) = n; <m, TdBound(n)>: dOcc(M) |]  ==> \
\     dBoundBy(<Cons(0, m), TdBound(n)>, <[], TdLam>, dLam(M))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac dBoundByI 1),
     (rtac (app_Nil RS sym) 4),
     (dtac dOcc_typeD1 4),
     (asm_simp_tac dTerm_ss 5),
     (REPEAT (ares_tac ([nat_succI, nat_0I] @ dOcc_dTermIs 
                        @ dTerm.intrs @ list.intrs) 1))]);

qed_goal "dBoundBy_dLamI2" dLambda.thy
    "dBoundBy(<m, T>, <l, U>, M) ==> \
\     dBoundBy(<Cons(0, m), T>, <Cons(0, l), U>, dLam(M))"
  (fn [prem] =>
    [(rtac (prem RS dBoundByE) 1),
     (safe_tac ZF_cs),
     (rtac dBoundByI 1),
     (rtac (app_Cons RS sym) 4),
     (asm_simp_tac dTerm_ss 4),
     (REPEAT (ares_tac ([nat_succI, nat_0I, initseg_ConsI] @ dOcc_dTermIs 
                      @ dTerm.intrs) 1))]);

qed_goal "dBoundBy_dAppI1" dLambda.thy
    "[| dBoundBy(<m, T>, <l, U>, A); B: dTerm |] ==> \
\     dBoundBy(<Cons(0, m), T>, <Cons(0, l), U>, dApp(A, B))"
  (fn [prem1, prem2] =>
    [(cut_facts_tac [prem2] 1),
     (rtac (prem1 RS dBoundByE) 1),
     (safe_tac ZF_cs),
     (rtac dBoundByI 1),
     (rtac (app_Cons RS sym) 4),
     (asm_simp_tac dTerm_ss 4),
     (REPEAT (ares_tac ([nat_succI, nat_0I, initseg_ConsI] @ dOcc_dTermIs 
                      @ dTerm.intrs) 1))]);

qed_goal "dBoundBy_dAppI2" dLambda.thy
    "[| dBoundBy(<m, T>, <l, U>, B); A: dTerm |] ==> \
\     dBoundBy(<Cons(1, m), T>, <Cons(1, l), U>, dApp(A, B))"
  (fn [prem1, prem2] =>
    [(cut_facts_tac [prem2] 1),
     (rtac (prem1 RS dBoundByE) 1),
     (safe_tac ZF_cs),
     (rtac dBoundByI 1),
     (rtac (app_Cons RS sym) 4),
     (asm_simp_tac dTerm_ss 4),
     (REPEAT (ares_tac ([nat_succI, nat_0I, initseg_ConsI] @ dOcc_dTermIs 
                      @ dTerm.intrs) 1))]);

val dBoundBy_dTermIs = [dBoundBy_dLamI1, dBoundBy_dLamI2,
                        dBoundBy_dAppI1, dBoundBy_dAppI2];

qed_goal "dBoundBy_dBoundE" dLambda.thy
    "dBoundBy(u, v, dBound(n)) ==> R"
  (fn [major] =>
    [(rtac (major RS dBoundByE) 1),
     (REPEAT (eresolve_tac dOcc_dTermEs 1)),
     (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs) 1)]);

qed_goal "dBoundBy_dVarE" dLambda.thy
    "dBoundBy(u, v, dVar(x)) ==> R"
  (fn [major] =>
    [(rtac (major RS dBoundByE) 1),
     (REPEAT (eresolve_tac dOcc_dTermEs 1)),
     (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs) 1)]);

qed_goal "dBoundBy_dLamE" dLambda.thy
    "[| dBoundBy(u, v, dLam(M)); \
\       !! m. [| u = <Cons(0, m), TdBound(dLamDeg(m, M))>; v = <[], TdLam>; \
\          M: dTerm; <m, TdBound(dLamDeg(m, M))>: dOcc(M) \
\       |] ==> R; \
\       !! l m n. [| u = <Cons(0, m), TdBound(n)>; v = <Cons(0, l), TdLam>; \
\          dBoundBy(<m, TdBound(n)>,  <l, TdLam>, M) \
\       |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS dBoundByE) 1),
     (eresolve_tac dTerm_typeEs 1),
     (rotate_tac 7 1),
     (eresolve_tac dOcc_dTermEs 1),
     (eresolve_tac dOcc_dTermEs 2),
     (rtac prem2 3),
     (rtac prem1 2),
     (safe_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs
              addSEs dTerm_typeEs addSEs list.free_SEs)),
     (ALLGOALS (asm_full_simp_tac (IFOL_ss addsimps [app_Nil, app_Cons]))),
     (safe_tac (ZF_cs addSEs list.free_SEs addSEs [ConsE])),
     (rotate_tac 3 1),
     (rotate_tac 3 2),
     (rotate_tac 3 3),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     (TRYALL hyp_subst_tac),
     (REPEAT (ares_tac [refl, dBoundByI, conjI] 1))]);

qed_goal "dBoundBy_dAppE" dLambda.thy
    "[| dBoundBy(u, v, dApp(A, B)); \
\       !! l m n. [| u = <Cons(0, m), TdBound(n)>; v = <Cons(0, l), TdLam>; \
\          dBoundBy(<m, TdBound(n)>,  <l, TdLam>, A); B: dTerm \
\       |] ==> R; \
\       !! l m n. [| u = <Cons(1, m), TdBound(n)>; v = <Cons(1, l), TdLam>; \
\          dBoundBy(<m, TdBound(n)>,  <l, TdLam>, B); A: dTerm \
\       |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS dBoundByE) 1),
     (eresolve_tac dTerm_typeEs 1),
     (eresolve_tac dOcc_dTermEs 1),
     (eresolve_tac dOcc_dTermEs 3),
     (eresolve_tac dOcc_dTermEs 2),
     (rtac prem2 7),
     (rtac prem1 3),
     (safe_tac (ZF_cs addSEs [ConsE]
              addSEs dTermOcc.Tag.free_SEs addSEs dOcc_dTermEs
              addSEs dTerm_typeEs addSEs list.free_SEs)),
     (ALLGOALS (asm_full_simp_tac (IFOL_ss addsimps [app_Nil, app_Cons]))),
     (safe_tac (ZF_cs addSEs list.free_SEs)),
     (ALLGOALS (rotate_tac 2)),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     (REPEAT (ares_tac [dBoundByI, refl] 1))]);

val dBoundBy_dTermEs = [dBoundBy_dVarE, dBoundBy_dBoundE,
                        dBoundBy_dLamE, dBoundBy_dAppE];

(** Some Lemmas **)

qed_goal "dDeg_dAbst_lemma1" dLambda.thy
    "[| M: dTerm; x ~: dFV(M); n: nat |] \
\       ==> dAbst(M, x, n) = M"
  (fn [major, prem1, prem2] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major] 1),
     (ALLGOALS (asm_simp_tac dTerm_ss))]);

qed_goal "dDeg_dAbst_lemma2" dLambda.thy
    "[| M: dTerm; x: dFV(M); n: nat |] \
\       ==> dDeg(dAbst(M, x, n)) = succ(n) Un dDeg(M)"
  (fn [major, prem1, prem2] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major] 1),
     (safe_tac (ZF_cs addSEs dProp_dTermEs addSEs dOcc_dTermEs
              addSEs dTermOcc.Tag.free_SEs)),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     (excluded_middle_tac "x: dFV(M)" 2),
     (excluded_middle_tac "x: dFV(N)" 3),
     (safe_tac ZF_cs),
     (ALLGOALS (asm_full_simp_tac 
                (dTerm_ss addsimps [dDeg_dAbst_lemma1]))),
     (ALLGOALS (fast_tac eq_cs))]);

qed_goal "dDeg_dLift_lemma1" dLambda.thy
    "[| dDeg(M) le n; M: dTerm; n: nat |] \
\       ==> dLift(M, n) = M"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (ALLGOALS (asm_simp_tac dTerm_ss))]);

qed_goal "dDeg_dLift_lemma2" dLambda.thy
    "[| n < dDeg(M); M: dTerm; n: nat |] \
\       ==> dDeg(dLift(M, n)) = succ(dDeg(M))"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (safe_tac ZF_cs),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     (rtac (dDeg_type RS natE) 1),
     (atac 1),
     (rotate_tac 4 2),
     (rotate_tac 4 1),
     (ALLGOALS (asm_full_simp_tac arith_ss)),
     (res_inst_tac [("i", "dDeg(N)"), ("j", "dDeg(M)")] Ord_linear_lt 1),
     (res_inst_tac [("i", "x"), ("j", "dDeg(M)")] Ord_linear2 5),
     (res_inst_tac [("i", "x"), ("j", "dDeg(N)")] Ord_linear2 3),
     (TRYALL (REPEAT o (ares_tac [nat_into_Ord, dDeg_type]))),
     (ALLGOALS (rotate_tac 6)),
     (ALLGOALS (asm_full_simp_tac 
                (dTerm_ss addsimps 
                 [dDeg_dLift_lemma1, lt_Un_eq_lemma, Un_absorb,
                  [Un_commute, lt_Un_eq_lemma] MRS trans]))),
     (rtac lt_Un_eq_lemma 2),
     (etac leI 2),
     (rtac ([Un_commute, lt_Un_eq_lemma] MRS trans) 1),
     (etac leI 1)]);

qed_goal "dDeg_dSubst_lemma1" dLambda.thy
    "[| M: dTerm; dDeg(M) le n; n: nat; N: dTerm |] \
\       ==> dSubst(M, n, N) = M"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major] 1),
     (safe_tac ZF_cs),
     (ALLGOALS (asm_full_simp_tac dTerm_ss))]);

qed_goal "dDeg_dSubst_lemma2" dLambda.thy
    "[| M: dTerm; n < dDeg(M); n: nat; N: dTerm |] \
\       ==> dDeg(dSubst(M, n, N)) le (dDeg(M) #- 1) Un dDeg(N)"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [major] 1),
     (safe_tac ZF_cs),
     (excluded_middle_tac "x = n" 2),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     (subgoal_tac "x < n" 1),
     (swap_res_tac [le_anti_sym] 2),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss addsimps 
                                   [[asm_rl, nat_into_Ord, nat_into_Ord] MRS
                                    not_lt_imp_le]))),
     (rtac Un_upper2_le 2),
     (rtac lt_trans2 1),
     (rtac Un_upper1_le 2),
     (rtac gt_pred 1),
     (REPEAT (ares_tac [le_refl, nat_into_Ord, dDeg_type] 1)),
    (* 16 *)
     (res_inst_tac [("M1", "M")] (dDeg_type RS natE) 1),
     (atac 1),
     (rotate_tac 5 1),
     (rotate_tac 5 2),
     (res_inst_tac [("i", "dDeg(M)"), ("j", "dDeg(N)")] Ord_linear_lt 3),
     (REPEAT (ares_tac [nat_into_Ord, dDeg_type] 3)),
     (forw_inst_tac [("c", "dDeg(M)")]
      ([Un_commute, lt_Un_eq_lemma] MRS trans) 5),
     (forw_inst_tac [("B", "dDeg(N)")] lt_Un_eq_lemma 3),
     (rotate_tac 8 3),
     (rotate_tac 7 4),
     (rotate_tac 8 5),
     (ALLGOALS (asm_full_simp_tac (arith_ss addsimps [Un_absorb]))),
     (rtac (nat_succ_Un RS subst) 1),
     (rtac (succ_pred RS mp RS ssubst) 3),
     (atac 5),
     (REPEAT (ares_tac [diff_type, nat_succI, nat_0I, dDeg_type] 1)),
    (* 31 *)
     (dtac (bspec RS bspec RS mp) 1),
     (etac le_trans 4),
     (asm_simp_tac arith_ss 3),
     (res_inst_tac [("M1", "xa")] (dDeg_type RS natE) 3),
     (asm_simp_tac (dTerm_ss addsimps [dDeg_dLift_lemma1]) 4),
     (rtac (dDeg_dLift_lemma2 RS ssubst) 5),
     (asm_simp_tac arith_ss 5),
     (REPEAT (ares_tac [nat_succI, Un_upper1_le, nat_into_Ord, dDeg_type,
                        nat_0I, dLift_type, le_refl, nat_UnI] 1)),
    (* 39 *)
     (res_inst_tac [("i", "x"), ("j", "dDeg(N)")] Ord_linear2 2),
     (res_inst_tac [("i", "x"), ("j", "dDeg(M)")] Ord_linear2 1),
     (TRYALL (REPEAT o (ares_tac [nat_into_Ord, dDeg_type]))),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss addsimps 
                                   [dDeg_dSubst_lemma1]))),
     (TRYALL (REPEAT o 
              ((dres_inst_tac [("x1", "xa")] 
                (bspec RS bspec RS mp)) THEN' atac THEN' atac 
               THEN' atac))),
     (safe_tac ZF_cs),
     (TRYALL (etac le_trans)),
     (TRYALL (rtac Un_least_lt)),
     (TRYALL (DEPTH_SOLVE_1 o 
              (fn i=>
               (rtac le_trans i) THEN
               ((resolve_tac [Un_upper1_le, Un_upper2_le] (i + 1)) THEN
                (resolve_tac [Un_upper1_le, Un_upper2_le, le_refl] i)) THEN
               (REPEAT (ares_tac 
                        [nat_into_Ord, dDeg_type, diff_type, nat_succI,
                        nat_0I, nat_UnI] i))))),
     (rtac le_trans 1),
     (rtac Un_upper1_le 2),
     (rtac le_trans 1),
     (rtac Un_upper2_le 2),
     (etac lt_imp_le_pred 1),
     (REPEAT (ares_tac [nat_into_Ord, dDeg_type, diff_type, nat_succI,
                        nat_0I, nat_UnI] 1)),
     (rtac le_trans 1),
     (rtac Un_upper1_le 2),
     (rtac le_trans 1),
     (rtac Un_upper1_le 2),
     (etac lt_imp_le_pred 1),
     (REPEAT (ares_tac [nat_into_Ord, dDeg_type, diff_type, nat_succI,
                        nat_0I, nat_UnI] 1))]);

qed_goal "dDeg_dSubst_lemma3" dLambda.thy
    "[| M: dTerm; dDeg(M) = 1; N: dProp |] ==> dSubst(M, 0, N): dProp"
  (fn [prem1, prem2, prem3] =>
    [(cut_facts_tac [prem1, prem2, prem3 RS dPropD1, prem3 RS dPropD2] 1),
     (cut_inst_tac [("M", "M"), ("n", "0"),
                    ("N", "N")] dDeg_dSubst_lemma2 1),
     (rtac (prem2 RS ssubst) 2),
     (REPEAT (ares_tac [le_refl, nat_0I, nat_into_Ord] 1)),
     (asm_full_simp_tac dTerm_ss 1),
     (REPEAT (ares_tac [dPropI, dSubst_type, nat_0I] 1))]);

qed_goal "dSubst_dAbst_lemma" dLambda.thy
    "[| M: dTerm; x: LVariable; n: nat; dDeg(M) le n |] ==> \
\       dSubst(dAbst(M, x, n), n, dVar(x)) = M"
  (fn [prem1, prem2, prem3, prem4] =>
    [(cut_facts_tac [prem2] 1),
     (rtac (prem4 RS rev_mp) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (ALLGOALS (rtac (impI RS ballI))),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_full_simp_tac dTerm_ss))]);

qed_goal "dSubst_dAbst_lemma2" dLambda.thy
    "[| M: dProp; x: LVariable |] ==> dSubst(dAbst(M, x, 0), 0, dVar(x)) = M"
  (fn [major,prem] =>
    [(rtac dSubst_dAbst_lemma 1),
     (rtac (major RS dPropD2 RS ssubst) 4),
     (REPEAT (ares_tac [major RS dPropD1, prem, nat_0I, Ord_0, le_refl] 1))]);

qed_goal "dSubst_dAbst_lemma3" dLambda.thy
    "[| dDeg(M) le n; M: dTerm; N: dTerm; n: nat |] \
\    ==> dSubst(dAbst(M, x, succ(n)), succ(n), N) = \
\               dSubst(dAbst(M, x, n), n, N)"
  (fn [prem1, prem2, prem3, prem4] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (rtac (prem4 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem2] 1),
     (rtac ballI 2),
     (excluded_middle_tac "xa = n" 2),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     (safe_tac lt_cs),
     (subgoals_tac ["succ(x) ~= n", "~ succ(x) < n"] 1),
     (asm_simp_tac dTerm_ss 1),
     (safe_tac lt_cs),
     (dtac (leI RS (succ_le_iff RS iffD1)) 2),
     (etac lt_irrefl 2),
     ((dtac lt_trans 1) THEN (atac 1)),
     (dtac (leI RS (succ_le_iff RS iffD1)) 1),
     (etac lt_irrefl 1)]);

qed_goal "dAbst_dSubst_lemma" dLambda.thy
    "[| M: dTerm; x: LVariable; x ~: dFV(M); n: nat; dDeg(M) le succ(n) |] \
\      ==> dAbst(dSubst(M, n, dVar(x)), x, n) = M"
  (fn [prem1, prem2, prem3, prem4, prem5] =>
    [(cut_facts_tac [prem2] 1),
     (rtac (prem3 RS rev_mp) 1),
     (rtac (prem5 RS rev_mp) 1),
     (rtac (prem4 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (ALLGOALS (rtac (impI RS ballI))),
     (excluded_middle_tac "xa = n" 2),
     (excluded_middle_tac "xa < n" 2),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     ((dtac lt_trans2 1) THEN (atac 1)),
     (etac lt_irrefl 1)]);


qed_goal "dAbst_dLift_lemma" dLambda.thy
    "[| m le n; M: dTerm; n: nat; m: nat \
\    |] ==> dAbst(dLift(M, m), x, succ(n)) \
\             = dLift(dAbst(M, x, n), m)"
  (fn [prem1, prem2, prem3, prem4] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (rtac (prem4 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem2] 1),
     (rtac (ballI RS ballI) 2),
     (rtac (ballI RS ballI) 1),
     (excluded_middle_tac "xa = n" 2),
     (excluded_middle_tac "n < xa" 2),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_simp_tac dTerm_ss))]);

qed_goal "dAbst_dSubst_lemma2" dLambda.thy
    "[| m le n; M: dTerm; \
\       N: dTerm; n: nat; m: nat \
\    |] ==> dAbst(dSubst(M, m, N), x, n) \
\             = dSubst(dAbst(M, x, succ(n)), m, dAbst(N, x, n))"
  (fn [prem1,prem3, prem4, prem5, prem6] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem4 RSN (2, bspec)) 1),
     (rtac (prem5 RSN (2, bspec)) 1),
     (rtac (prem6 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem3] 1),
     (rtac (ballI RS ballI RS ballI) 2),
     (rtac (ballI RS ballI RS ballI) 1),
     (excluded_middle_tac "xa = n" 2),
     (excluded_middle_tac "xa < n" 2),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_simp_tac (dTerm_ss addsimps [dAbst_dLift_lemma])))]);

qed_goal "dLift_dLift_lemma" dLambda.thy
    "[| m le n; M: dTerm; n: nat; m: nat |] ==> \
\      dLift(dLift(M, m), succ(n)) = dLift(dLift(M, n), m)"
  (fn [prem1, prem2, prem4, prem5] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem4 RSN (2, bspec)) 1),
     (rtac (prem5 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem2] 1),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (safe_tac ZF_cs),
     (excluded_middle_tac "n < x" 1),
     (subgoal_tac "n < xa" 2),
     (etac lt_trans2 3),
     (atac 3),
     (excluded_middle_tac "n < xa" 1),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss addsimps 
                              [leI, [nat_into_Ord, nat_into_Ord] 
                               MRS not_lt_iff_le])))]);
  
qed_goal "dLift_dSubst_lemma" dLambda.thy
    "[| m le n; M: dTerm; N: dTerm; n: nat; m: nat |] ==> \
\      dLift(dSubst(M, n, N), m) = dSubst(dLift(M, m), succ(n), \
\                                         dLift(N, m))"
  (fn [prem1, prem2, prem3, prem4, prem5] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (rtac (prem4 RSN (2, bspec)) 1),
     (rtac (prem5 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem2] 1),
     (ALLGOALS (asm_simp_tac (dTerm_ss addsimps [dLift_dLift_lemma]))),
     (safe_tac ZF_cs),
     (excluded_middle_tac "n < x" 1),
     (subgoal_tac "n < xa" 2),
     (etac lt_trans2 3),
     (atac 3),
     (excluded_middle_tac "n < xa" 1),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss addsimps 
                              [leI, [nat_into_Ord, nat_into_Ord] 
                               MRS not_lt_iff_le]))),
     (excluded_middle_tac "xa = n" 1),
     (subgoals_tac ["xa < n", "x < n", "~n #- 1 < x"] 1),
     (rtac notI 2),
     (dtac diff_ltD 2),
     (asm_full_simp_tac dTerm_ss 5),
     (swap_res_tac [le_anti_sym] 5),
     (REPEAT (ares_tac [nat_succI, nat_0I, le_trans] 2)),
     (etac lt_trans1 2),
     (atac 2),
     (fast_tac lt_cs 2),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss addsimps [leI]))),
     (rtac (succ_pred RS mp RS ssubst) 1),
     (atac 3),
     (REPEAT (ares_tac [refl] 1))]);

qed_goal "dSubst_dSubst_lemma1" dLambda.thy
    "[| dDeg(M) le succ(m); dDeg(A) = 0; m le n; \
\       M: dTerm; A: dTerm; B: dTerm; n: nat; m: nat |] ==> \
\       dSubst(dSubst(M, m, A), n, B) = \
\               dSubst(dSubst(M, succ(n), dLift(B, 0)), m, A)"
  (fn [prema, prem0, prem1, prem2, prem3, prem4, prem5, prem6] =>
    [(rtac (prema RS rev_mp) 1),
     (rtac (prem0 RS rev_mp) 1),
     (rtac (prem1 RS rev_mp) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (rtac (prem4 RSN (2, bspec)) 1),
     (rtac (prem5 RSN (2, bspec)) 1),
     (rtac (prem6 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem2] 1),
     (ALLGOALS (asm_simp_tac (dTerm_ss addsimps [dDeg_dLift_lemma1]))),
     (safe_tac ZF_cs),
     (excluded_middle_tac "x = n" 1),
     (subgoals_tac ["n < x", "n < xa"] 1),
     (swap_res_tac [le_anti_sym] 3),
     ((etac lt_trans2 2) THEN (atac 2)),
     (hyp_subst_tac 4),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss addsimps 
                                   [leI, dDeg_dSubst_lemma1,
                                    [nat_into_Ord, nat_into_Ord] 
                                    MRS not_lt_iff_le])))]);

qed_goal "dSubst_dSubst_lemma2" dLambda.thy
    "[| dDeg(B) = 0; m le n; \
\       M: dTerm; A: dTerm; B: dTerm; n: nat; m: nat |] ==> \
\       dSubst(dSubst(M, m, A), n, B) = \
\               dSubst(dSubst(M, succ(n), B), m, dSubst(A, n, B))"
  (fn [prem0, prem1, prem2, prem3, prem4, prem5, prem6] =>
    [(rtac (prem0 RS rev_mp) 1),
     (rtac (prem1 RS rev_mp) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (rtac (prem4 RSN (2, bspec)) 1),
     (rtac (prem5 RSN (2, bspec)) 1),
     (rtac (prem6 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem2] 1),
     (ALLGOALS (asm_simp_tac (dTerm_ss addsimps [dDeg_dLift_lemma1,
                                                 dLift_dSubst_lemma]))),
     (safe_tac ZF_cs),
     (res_inst_tac [("i", "n"), ("j", "x")] Ord_linear_lt 1),
     (REPEAT (ares_tac [nat_into_Ord] 1)),
     (subgoal_tac "n < xa" 1),
     ((etac lt_trans2 2) THEN (atac 2)),
     (res_inst_tac [("i", "n"), ("j", "succ(xa)")] Ord_linear_lt 3),
     (REPEAT (ares_tac [nat_into_Ord, nat_succI] 3)),
     (subgoal_tac "succ(x) < n" 5),
     (subgoal_tac "xa ~= n #- 1" 3),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss addsimps 
                                   [leI, dDeg_dSubst_lemma1,
                                    [nat_into_Ord, nat_into_Ord] 
                                    MRS not_lt_iff_le]))),
     (res_inst_tac [("j", "succ(xa)")] lt_trans1 2),
     (atac 3),
     (eres_inst_tac [("n", "n")] natE 1),
     (safe_tac ZF_cs),
     (rotate_tac 8 2),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     (etac lt_irrefl 1)]);

qed_goal "dFV_dAbst" dLambda.thy
    "[| M: dTerm; n:nat |] ==> dFV(dAbst(M, x, n)) = dFV(M) - {x}"
  (fn [major, prem] =>
    [(rtac (prem RS rev_bspec) 1),
     (dTermOcc.ind_tac "M" [major] 1),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (ALLGOALS (fast_tac eq_cs))]);

qed_goal "dDeg_dLamDeg_lemma1" dLambda.thy
    "[| M: dTerm; <l, TdBound(n)>: dOcc(M) |] ==> \
\        n < dDeg(M) #+ dLamDeg(l, M)"
  (fn [prem1, prem2] =>
    [(rtac (prem2 RS rev_mp) 1),
     (res_inst_tac [("x", "l")] spec 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs dTermOcc.Tag.free_SEs)),
     (TRYALL ((forward_tac [dOcc_typeD1]) THEN' atac)),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (rtac (dDeg_type RS natE) 1),
     (atac 1),
     (rotate_tac 4 1),
     (rotate_tac 4 2),
     (asm_full_simp_tac (arith_ss addsimps [add_succ_right, add_0_right]) 1),
     (asm_full_simp_tac (arith_ss addsimps [add_succ_right, add_0_right]) 2),
     (ALLGOALS ((dtac (spec RS mp)) THEN' atac)),
     (etac leI 1),
     (ALLGOALS (etac lt_trans2)),
     (ALLGOALS (rtac add_le_mono1)),
     (REPEAT (ares_tac [dLamDeg_type, dDeg_type, nat_UnI, 
                      Un_upper1_le, Un_upper2_le, nat_into_Ord] 1))]);

qed_goal "dDeg_0_lemma" dLambda.thy
    "[| M: dTerm; ~(EX l n. <l, TdBound(n)>: dOcc(M)) |] ==> dDeg(M) = 0"
  (fn [prem1, prem2] =>
    [(rtac (prem2 RS rev_mp) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (REPEAT (ares_tac ([exI] @ dOcc_dTermIs) 1)),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs dTermOcc.Tag.free_SEs)),
     (asm_simp_tac arith_ss 2),
     (asm_simp_tac ZF_ss 5),
     (ALLGOALS (fast_tac (ZF_cs addIs dOcc_dTermIs)))]);

qed_goal "dDeg_dLamDeg_lemma2" dLambda.thy
    "[| M: dTerm; EX l n. <l, TdBound(n)>: dOcc(M) |] ==> \
\        EX l n. <l, TdBound(n)>: dOcc(M) & \
\                dDeg(M) = succ(n) #- dLamDeg(l, M)"
  (fn [prem1, prem2] =>
    [(rtac (prem2 RS rev_mp) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs dTermOcc.Tag.free_SEs)),
     (TRYALL ((swap_res_tac [exI RS exI]) THEN' atac)),
     (rtac (exI RS exI) 1),
     (resolve_tac (dOcc_dTermIs RL [conjI]) 1),
     (asm_simp_tac dTerm_ss 1),
     (res_inst_tac [("x", "Cons(0, lb)")] exI 1),
     ((forw_inst_tac [("l", "lb")] dOcc_typeD1 1) THEN (atac 1)),
     ((forw_inst_tac [("T", "TdBound(na)")] dOcc_typeD2 1) THEN (atac 1)),
     (eresolve_tac dTag_typeEs 1),
     (res_inst_tac [("x", "Cons(1, la)")] exI 2),
     ((forw_inst_tac [("l", "la")] dOcc_typeD1 2) THEN (atac 2)),
     (res_inst_tac [("x", "Cons(0, la)")] exI 3),
     ((forw_inst_tac [("l", "la")] dOcc_typeD1 3) THEN (atac 3)),
     (TRYALL ((rtac exI) THEN' (rtac conjI) THEN'
            (eresolve_tac dOcc_dTermIs))),
     (ALLGOALS (asm_simp_tac (dTerm_ss
                            addsimps [dDeg_0_lemma]))),
    (* 17 *)
     (ALLGOALS ((forw_inst_tac [("l", "la")] dOcc_typeD1) THEN' atac)),
     (ALLGOALS ((forw_inst_tac [("l", "lb")] dOcc_typeD1) THEN' atac)),
     (ALLGOALS ((forw_inst_tac [("l", "lc")] dOcc_typeD1) THEN' atac)),
     (ALLGOALS (rtac Ord_linear_le)),
     (res_inst_tac [("x", "Cons(0, la)")] exI 8),
     (res_inst_tac [("x", "Cons(1, lb)")] exI 7),
     (res_inst_tac [("x", "Cons(0, la)")] exI 4),
     (res_inst_tac [("x", "Cons(1, lb)")] exI 3),
     (TRYALL ((rtac exI) THEN' (rtac conjI) THEN'
            (eresolve_tac dOcc_dTermIs))),
     (etac (le_Un_eq_lemma RS trans) 7),
     (etac (le_Un_eq_lemma RS trans) 3),
     (rtac (Un_commute RS trans) 8),
     (etac (le_Un_eq_lemma RS trans) 8),
     (rtac (Un_commute RS trans) 4),
     (etac (le_Un_eq_lemma RS trans) 4),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (REPEAT ((ares_tac [nat_into_Ord, diff_type, nat_succI, dLamDeg_type] 1)
            ORELSE ((dtac dOcc_typeD2 1) THEN 
                    (eresolve_tac dTag_typeEs 2))))]);

qed_goal "dBoundBy_dLamDeg_lemma1" dLambda.thy
    "dBoundBy(<l, TdBound(n)>, v, M) ==> succ(n) #- dLamDeg(l, M) = 0"
  (fn [major] =>
    [(rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "v")] spec 1),
     (res_inst_tac [("x", "l"), ("A", "list(nat)")] bspec 1),
     (res_inst_tac [("x", "n"), ("A", "nat")] bspec 1),
     (rtac (major RS dBoundByE) 2),
     (rtac (major RS dBoundByE) 3),
     (dTermOcc.ind_tac "M" [major RS dBoundByD1] 1),
     (safe_tac (ZF_cs addSEs dBoundBy_dTermEs addSEs dTermOcc.Tag.free_SEs
              addSEs [ConsE])),
     (REPEAT (ares_tac [app_type] 6)),
     (dtac dOcc_typeD2 5),
     (eresolve_tac dTag_typeEs 6),
     (REPEAT (atac 5)),
     (ALLGOALS (asm_simp_tac (dTerm_ss addsimps [diff_self_eq_0]))),
     (dtac (bspec RS bspec RS spec RS mp) 1),
     (atac 3),
     (asm_full_simp_tac (IFOL_ss addsimps [le0_iff RS iff_sym]) 3),
     (rtac le_trans 3),
     (atac 4),
     (REPEAT (ares_tac [diff_le_mono1, dLamDeg_type, le_refl, 
                      nat_into_Ord, nat_succI, leI] 1))]);

qed_goal "dBoundBy_dLamDeg_lemma2" dLambda.thy
    "[| M: dTerm; <l, TdBound(n)>: dOcc(M); n < dLamDeg(l, M) |] \
\      ==> EX m. dBoundBy(<l, TdBound(n)>, <m, TdLam>, M)"
  (fn [major, prem1, prem2] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem2 RS rev_mp) 1),
     (res_inst_tac [("x", "l"), ("A", "list(nat)")] bspec 1),
     (res_inst_tac [("x", "n"), ("A", "nat")] bspec 1),
     (cut_facts_tac [[prem1, major] MRS dOcc_typeD2] 2),
     (rtac ([prem1, major] MRS dOcc_typeD1) 3),
     (dTermOcc.ind_tac "M" [major] 1),
     (safe_tac (ZF_cs addSEs dTag_typeEs addSEs dOcc_dTermEs addSEs [ConsE]
              addSEs dTermOcc.Tag.free_SEs)),
     (rotate_tac 4 2),
     (rotate_tac 6 3),
     (rotate_tac 6 4),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     (etac FalseE 1),
     (etac leE 1),
     (hyp_subst_tac 2),
     (rtac exI 2),
     (REPEAT (ares_tac [refl, dBoundBy_dLamI1] 2)),
     (ALLGOALS ((dtac (bspec RS bspec RS mp RS mp)) THEN' 
              (fn i=> (atac (i + 2))))),
     (safe_tac ZF_cs),
     (REPEAT (ares_tac [exI, dBoundBy_dLamI2, dBoundBy_dAppI1, 
                      dBoundBy_dAppI2] 1))]);


qed_goal "dProp_dBoundBy_lemma1" dLambda.thy
    "[| M: dProp; <m, TdBound(n)>: dOcc(M) |] ==> \
\      EX l. dBoundBy(<m, TdBound(n)>, <l, TdLam>, M)"
  (fn [major, prem] =>
    [(rtac (major RS dPropE) 1),
     (cut_facts_tac [[major RS dPropD1, prem] MRS dDeg_dLamDeg_lemma1] 1),
     (rtac dBoundBy_dLamDeg_lemma2 1),
     (asm_full_simp_tac arith_ss 3),
     (REPEAT (ares_tac [prem] 1))]);

qed_goal "dProp_dBoundBy_lemma2" dLambda.thy
    "[| M: dTerm; ALL m n. <m, TdBound(n)>: dOcc(M) --> \
\         (EX l. dBoundBy(<m, TdBound(n)>, <l, TdLam>, M)) |] ==> M: dProp"
  (fn [major, prem] =>
    [(excluded_middle_tac "EX l n. <l, TdBound(n)>: dOcc(M)" 1),
     (dtac (major RS dDeg_0_lemma) 1),
     (dtac (major RS dDeg_dLamDeg_lemma2) 2),
     (REPEAT (eresolve_tac [exE, conjE] 2)),
     (rtac (prem RS spec RS spec RS mp RS exE) 2),
     (atac 2),
     (dtac dBoundBy_dLamDeg_lemma1 2),
     (rotate_tac 2 2),
     (asm_full_simp_tac IFOL_ss 2),
     (REPEAT (ares_tac [dPropI, major] 1))]);

qed_goal "dOcc_dAbstI1" dLambda.thy
    "[| <l, TdVar(x)>: dOcc(M); M: dTerm; n: nat |] \
\       ==> <l, TdBound(n #+ dLamDeg(l, M))>: dOcc(dAbst(M, x, n))"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem1 RS rev_mp) 1),
     (res_inst_tac [("x", "l"), ("A", "list(nat)")] bspec 1),
     (rtac ([prem1, prem2] MRS dOcc_typeD1) 2),
     (rtac (prem3 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem2] 1),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs dTermOcc.Tag.free_SEs
              addSEs [ConsE])),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (ALLGOALS (resolve_tac dOcc_dTermIs)),
     (dtac (bspec RS bspec RS mp) 1),
     (atac 3),
     (etac nat_succI 1),
     (asm_full_simp_tac arith_ss 2),
     (atac 1),
     (ALLGOALS (etac (bspec RS bspec RS mp))),
     (REPEAT (atac 1))]);

qed_goal "dOcc_dAbstI2" dLambda.thy
    "[| <l, T>: dOcc(M); T ~= TdVar(x); M: dTerm; n: nat |] \
\       ==> <l, T>: dOcc(dAbst(M, x, n))"
  (fn [prem1, major, prem2, prem3] =>
    [(cut_facts_tac [major] 1),
     (rtac (prem1 RS rev_mp) 1),
     (res_inst_tac [("x", "l"), ("A", "list(nat)")] bspec 1),
     (rtac ([prem1, prem2] MRS dOcc_typeD1) 2),
     (rtac (prem3 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem2] 1),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs dTermOcc.Tag.free_SEs
              addSEs [ConsE])),
     (subgoals_tac ["x ~= xa"] 1),
     (fast_tac ZF_cs 2),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (ALLGOALS (resolve_tac dOcc_dTermIs)),
     (dtac (bspec RS bspec RS mp) 1),
     (atac 3),
     (etac nat_succI 1),
     (REPEAT (atac 1)),
     (ALLGOALS (etac (bspec RS bspec RS mp))),
     (REPEAT (atac 1))]);

qed_goal "dOcc_dAbstE_lemma" dLambda.thy
    "[| <l, T>: dOcc(dAbst(M, x, n)); M: dTerm; n: nat; \
\     T = TdBound(n #+ dLamDeg(l, M)) & <l, TdVar(x)>: dOcc(M) --> R; \
\     <l, T>: dOcc(M) --> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3, prem4] =>
    [(rtac (prem4 RS rev_mp) 1),
     (rtac (prem3 RS rev_mp) 1),
     (rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "l"), ("A", "list(nat)")] bspec 1),
     (rtac (major RS dOcc_typeD1) 2),
     (REPEAT (ares_tac [dAbst_type, prem1, prem2] 2)),
     (rtac (prem2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs dTermOcc.Tag.free_SEs
              addSEs [ConsE])),
     (asm_simp_tac dTerm_ss 1),
     (TRYALL (swap_res_tac dOcc_dTermIs)),
     (TRYALL (swap_res_tac dOcc_dTermIs)),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     (dtac (bspec RS bspec) 2),
     (etac nat_succI 2),
     (dtac (bspec RS bspec) 1),
     (etac nat_succI 1),
     (TRYALL (dtac (bspec RS bspec))),
     (TRYALL atac),
     (ALLGOALS (asm_full_simp_tac arith_ss)),
     (REPEAT (fast_tac ZF_cs 1))]);

qed_goal "dOcc_dAbstE" dLambda.thy
    "[| <l, T>: dOcc(dAbst(M, x, n)); M: dTerm; n: nat; \
\     [| T = TdBound(n #+ dLamDeg(l, M)); <l, TdVar(x)>: dOcc(M) |] ==> R; \
\     <l, T>: dOcc(M) ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2, prem3, prem4] =>
    [(rtac ([major, prem1, prem2] MRS dOcc_dAbstE_lemma) 1),
     (ALLGOALS (rtac impI)),
     (etac conjE 1),
     (etac prem4 2),
     (etac prem3 1),
     (atac 1)]);

qed_goal "dOcc_dAbst_lemma1" dLambda.thy
    "[| <l, T>: dOcc(dAbst(M, x, n)); M: dTerm; n: nat |] ==> T ~= TdVar(x)"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS rev_mp) 1),
     (res_inst_tac [("x", "l")] spec 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs dTermOcc.Tag.free_SEs)),
     (ALLGOALS ((dtac (bspec RS spec RS mp)) THEN' (fn i=> atac (i + 1)))),
     (etac nat_succI 1),
     (TRYALL atac),
     (ALLGOALS (etac notE)),
     (ALLGOALS (rtac refl))]);

qed_goal "dOcc_dAbst_lemma2" dLambda.thy
    "[| <l, TdBound(n #+ dLamDeg(l, M))>: dOcc(dAbst(M, x, n)); \
\    M: dTerm; n: nat; dDeg(M) le n |] ==>  <l, TdVar(x)>: dOcc(M)"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (prem3 RS rev_mp) 1),
     (res_inst_tac [("x", "l"), ("A", "list(nat)")] bspec 1),
     (rtac (major RS dOcc_typeD1) 2),
     (REPEAT (ares_tac [dAbst_type, prem1, prem2] 2)),
     (rtac (prem2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs dTermOcc.Tag.free_SEs
              addSEs [ConsE])),
     (rotate_tac 5 3),
     (rotate_tac 8 4),
     (rotate_tac 8 5),
     (ALLGOALS (asm_full_simp_tac dTerm_ss)),
     (etac FalseE 2),
    (* 15 *)
     (ALLGOALS (resolve_tac dOcc_dTermIs)),
     (ALLGOALS (etac (bspec RS bspec RS mp RS mp))),
     (atac 3),
     (asm_simp_tac arith_ss 3),
     (REPEAT ((ares_tac [nat_succI, nat_into_Ord,
                       dDeg_type] 1) ORELSE
            (etac Un_least_ltE 1)))]);

qed_goal "dOcc_dAbst_lemma3" dLambda.thy
    "[| <l, TdBound(dLamDeg(l, M))>: dOcc(dAbst(M, x, 0)); M: dProp |] \
\      ==> <l, TdVar(x)>: dOcc(M)"
  (fn [major, prem] =>
    [(rtac (prem RS dPropE) 1),
     (rtac dOcc_dAbst_lemma2 1),
     (asm_simp_tac IFOL_ss 4),
     (rtac le_refl 4),
     (asm_simp_tac arith_ss 1),
     (REPEAT (ares_tac [major, nat_0I, Ord_0] 1))]);

qed_goal "dLamDeg_dAbst_lemma" dLambda.thy
    "[| M: dTerm; <l, T>: dOcc(M); n: nat |] ==> \
\        dLamDeg(l, dAbst(M, x, n)) = dLamDeg(l, M)"
  (fn [major, prem1, prem2] =>
    [(rtac (prem1 RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (res_inst_tac [("x", "l"), ("A", "list(nat)")] bspec 1),
     (rtac ([prem1, major] MRS dOcc_typeD1) 2),
     (dTermOcc.ind_tac "M" [major] 1),
     (safe_tac (ZF_cs addSEs dOcc_dTermEs addSEs [ConsE]
              addSEs dTermOcc.Tag.free_SEs)),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_simp_tac dTerm_ss))]);

qed_goal "dBoundBy_dAbstI" dLambda.thy
    "[| dBoundBy(u, v, M); n: nat |] ==> dBoundBy(u, v, dAbst(M, x, n))"
  (fn [major, prem] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (prem RSN (2, bspec)) 1),
     (res_inst_tac [("x", "v")] spec 1),
     (res_inst_tac [("x", "u")] spec 1),
     (dTermOcc.ind_tac "M" [major RS dBoundByD1] 1),
     (safe_tac (ZF_cs addSEs dBoundBy_dTermEs
              addSEs dTermOcc.Tag.free_SEs)),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (ALLGOALS (resolve_tac dBoundBy_dTermIs)),
     (rtac dLamDeg_dAbst_lemma 2),
     (TRYALL (REPEAT o (ares_tac [dAbst_type, nat_succI]))),
     (etac dOcc_dAbstI2 1),
     (fast_tac (ZF_cs addSEs dTermOcc.Tag.free_SEs) 1),
     (REPEAT (ares_tac [nat_succI] 1)),
     (ALLGOALS (etac (spec RS spec RS bspec RS mp))),
     (REPEAT (ares_tac [nat_succI] 1))]);

qed_goal "dBoundBy_dAbstD" dLambda.thy
    "[| dBoundBy(u, v, dAbst(M, x, n)); M: dTerm; n: nat |] \
\        ==> dBoundBy(u, v, M)"
  (fn [major, prem1, prem2] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (res_inst_tac [("x", "v")] spec 1),
     (res_inst_tac [("x", "u")] spec 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (excluded_middle_tac "x = xa" 1),
     (ALLGOALS (asm_simp_tac dTerm_ss)),
     (safe_tac (ZF_cs addSEs dBoundBy_dTermEs addSEs [dOcc_dAbstE]
              addSEs dTermOcc.Tag.free_SEs)),
     (etac nat_succI 1),
     (ALLGOALS (resolve_tac dBoundBy_dTermIs)),
     (TRYALL atac),
     (REPEAT (ares_tac [dLamDeg_dAbst_lemma RS sym, nat_succI] 1)),
     (dres_inst_tac [("f", "%x. x #- dLamDeg(m, M)")] function_apply_eq 1),
     (asm_full_simp_tac (dTerm_ss addsimps [dLamDeg_dAbst_lemma,
                                          diff_self_eq_0]) 1),
     (dtac (sym RS diff_eq_0D) 1),
     (asm_full_simp_tac dTerm_ss 3),
     (subgoal_tac "dLamDeg(m, M) < dLamDeg(m, M)" 3),
     (rtac lt_trans1 4),
     (atac 5),
     (rtac add_le_self2 4),
     (etac lt_irrefl 3),
     (REPEAT (ares_tac [nat_succI, dLamDeg_type, add_type,
                      dLamDeg_dAbst_lemma RS sym] 1)),
     (ALLGOALS (etac (spec RS spec RS bspec RS mp))),
     (atac 2),
     (REPEAT (ares_tac [nat_succI] 1))]);


qed_goal "dFV_dLift_iff" dLambda.thy
    "[| M: dTerm; n: nat |] \
\       ==> x : dFV(dLift(M, n)) <-> x: dFV(M)"
  (fn [prem1, prem2] =>
    [(rtac (prem2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (rtac ballI 2),
     (excluded_middle_tac "n < xa" 2),
     (ALLGOALS (asm_simp_tac dTerm_ss))]);

qed_goal "dFV_dSubst_lemma" dLambda.thy
    "[| x: dFV(dSubst(M, n, N)); M: dTerm; n: nat; N: dTerm |] ==> \
\        x: dFV(M) | x: dFV(N)"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (dTermOcc.ind_tac "M" [prem1] 1),
     (rtac ballI 2),
     (excluded_middle_tac "xa = n" 2),
     (excluded_middle_tac "xa < n" 2),
     (ALLGOALS (asm_full_simp_tac (dTerm_ss))),
     (safe_tac ZF_cs),
     (ALLGOALS (fn i => (dtac (bspec RS bspec RS mp) i) THEN
              (atac (i + 2)))),
     (TRYALL (REPEAT o (ares_tac [dLift_type, nat_succI, nat_0I]))),
     (asm_full_simp_tac (dTerm_ss addsimps [dFV_dLift_iff]) 1),
     (safe_tac ZF_cs)]);
