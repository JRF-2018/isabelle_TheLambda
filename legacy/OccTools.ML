(*
    File:        OccTools.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open OccTools;

val list_free_simps = [Cons_iff]  @ 
    (map list.mk_free ["Cons(a, l) = [] <-> False",
                       "[] = Cons(a, l) <-> False"]);

qed_goal "Prod_domain_0_eq" ZF.thy
    "domain(0)*A = 0"
  (fn _ =>
    [(rtac (domain_0 RS ssubst) 1),
     (rtac Sigma_empty1 1)]);

(** list_op **)
qed_goalw "list_op_bnd_mono" OccTools.thy [list_op_def, 
                                            list_dom_def, bnd_mono_def]
    "bnd_mono(list_dom(A), list_op(A))"
  (fn _ =>
    [(rtac (rewrite_rule [bnd_mono_def] list.bnd_mono) 1)]);

qed_goalw "list_op_lfp_eq" OccTools.thy ([list_op_def, list_dom_def,
                                 lfp_def] @ list.defs)
    "list(A) = lfp(list_dom(A), list_op(A))"
  (fn _ =>
    [(rtac refl 1)]);


qed_goalw "list_op_continuous" OccTools.thy [list_op_def, list_dom_def]
    "X~= 0 ==> list_op(A, Union(X)) = (UN x: X. list_op(A, x))"
  (fn [prem] =>
    [(rtac (prem RS not_emptyE) 1),
     (rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addIs list.intrs addSEs list.free_SEs)))]);

(** Occ_shift **)
qed_goalw "Occ_shiftI" OccTools.thy [Occ_shift_def]
    "<l, T>: X ==> <Cons(b, l), T>: Occ_shift(b, X)"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac ZF_cs 1)]);

qed_goalw "Occ_shiftE" OccTools.thy [Occ_shift_def]
    "[| x: Occ_shift(b, X); \
\       !!l T. [| x = <Cons(b, l), T>; <l, T>: X |] ==> R |] ==> R"
  (fn major::prems =>
    [(rtac (major RS ReplaceE) 1),
     (REPEAT (eresolve_tac [conjE, exE] 1)),
     (resolve_tac prems 1),
     (atac 1),
     (REPEAT (hyp_subst_tac 1)),
     (atac 1)]);

qed_goal "Occ_shiftE2" OccTools.thy
    "[| <l, T>: Occ_shift(b, X); \
\       !!m. [| l = Cons(b, m); <m, T>: X |] ==> R |] ==> R"
  (fn major::prems =>
    [(rtac (major RS Occ_shiftE) 1),
     (etac (Pair_iff RS iffD1 RS conjE) 1),
     (eresolve_tac prems 1),
     (hyp_subst_tac 1),
     (atac 1)]);

qed_goalw "Occ_shift_0" OccTools.thy [Occ_shift_def]
    "Occ_shift(b, 0) = 0"
  (fn _ =>
    [(fast_tac eq_cs 1)]);

qed_goalw "Occ_shift_cons" OccTools.thy [Occ_shift_def]
    "Occ_shift(b, cons(<l, T>, X)) = cons(<Cons(b, l), T>, Occ_shift(b, X))"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac ZF_cs))]);

qed_goalw "Occ_shift_continuous" OccTools.thy [Occ_shift_def]
    "Occ_shift(b, Union(X)) = (UN x: X. Occ_shift(b, x))"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac ZF_cs))]);

qed_goalw "Occ_shift_Un" OccTools.thy [Occ_shift_def]
    "Occ_shift(b, X Un Y) = Occ_shift(b, X) Un Occ_shift(b, Y)"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac ZF_cs))]);

qed_goal "Occ_shift_iff" OccTools.thy
    "[| X <= A*B; Y <= C*D; X ~= 0 |] ==> \
\         Occ_shift(a, X) = Occ_shift(b, Y) <-> a = b & X = Y"
  (fn [domX, domY, not_emptyX] =>
    [(rtac iffI 1),
     (rtac conjI 1),
     (dtac equalityD1 1),
     (rtac (not_emptyX RS not_emptyE) 1),
     (forward_tac [domX RS subsetD] 1),
     (etac SigmaE 1),
     (hyp_subst_tac 1),
     (dtac subsetD 1),
     (etac Occ_shiftI 1),
     (etac Occ_shiftE2 1),
     (etac (Cons_iff RS iffD1 RS conjunct1) 1),
     (rtac equalityI 1),
     (dtac equalityD1 1),
     (dtac equalityD2 2),
     (REPEAT ((rtac subsetI 1) THEN
              (forward_tac [domX RS subsetD, domY RS subsetD] 1) THEN
              (etac SigmaE 1) THEN
              (hyp_subst_tac 1) THEN
              (dtac subsetD 1) THEN
              (etac Occ_shiftI 1) THEN
              (etac Occ_shiftE2 1) THEN
              (dtac (Cons_iff RS iffD1 RS conjunct2) 1) THEN
              (hyp_subst_tac 1) THEN
              (atac 1))),
     (etac conjE 1),
     (hyp_subst_tac 1),
     (rtac refl 1)]);

val Occ_shift_simps = [Occ_shift_0, Occ_shift_cons, Occ_shift_Un,
                      Occ_shift_iff];

(** Occ_subtree **)
qed_goalw "Occ_subtreeI" OccTools.thy [Occ_subtree_def]
    "<Cons(b, l), T>: X ==> <l, T>: Occ_subtree(b, X)"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (rtac ReplaceI 1),
     (atac 2),
     (REPEAT (resolve_tac [refl, conjI, exI] 1)),
     (asm_full_simp_tac (IFOL_ss addsimps [Pair_iff, Cons_iff]) 1),
     (REPEAT (eresolve_tac [exE, conjE] 1)),
     (REPEAT (hyp_subst_tac 1)),
     (rtac refl 1)]);

qed_goalw "Occ_subtreeD" OccTools.thy [Occ_subtree_def]
    "<l, T>: Occ_subtree(b, X) ==> <Cons(b, l), T>: X"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac ZF_cs 1)]);

qed_goalw "Occ_subtreeE" OccTools.thy [Occ_subtree_def]
    "[| x: Occ_subtree(b, X); \
\       !!l T. [| x = <l, T>; <Cons(b, l), T>: X |] ==> R |] ==> R"
  (fn major::prems =>
    [(rtac (major RS ReplaceE) 1),
     (REPEAT (eresolve_tac [conjE, exE] 1)),
     (resolve_tac prems 1),
     (atac 1),
     (REPEAT (hyp_subst_tac 1)),
     (atac 1)]);

val Occ_subtreeE2 = standard(make_elim(Occ_subtreeD));

qed_goalw "Occ_subtree_0" OccTools.thy [Occ_subtree_def]
    "Occ_subtree(b, 0) = 0"
  (fn _ =>
    [(fast_tac eq_cs 1)]);

qed_goalw "Occ_subtree_cons_Nil" OccTools.thy [Occ_subtree_def]
    "Occ_subtree(a, cons(<[], T>, X)) = Occ_subtree(a, X)"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSEs list.free_SEs)))]);

qed_goal "Occ_subtree_cons_Cons" OccTools.thy
    "Occ_subtree(a, cons(<Cons(b, l), T>, X)) = \
\            if(a = b, cons(<l, T>, Occ_subtree(b, X)), Occ_subtree(a, X))"
  (fn _ =>
    [(res_inst_tac [("Q", "a = b")] (excluded_middle RS disjE) 1),
     (rtac (if_not_P RS sym RSN (2, trans)) 1),
     (atac 2),
     (rtac (if_P RS sym RSN (2, trans)) 2),
     (atac 3),
     (ALLGOALS (rtac equalityI)),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_subtreeI] addSEs [Occ_subtreeE] 
                        addSDs [Cons_iff RS iffD1])))]);

qed_goal "Occ_subtree_continuous" OccTools.thy
    "Occ_subtree(b, Union(X)) = (UN x: X. Occ_subtree(b, x))"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_subtreeI] addSEs [Occ_subtreeE] 
                        addSDs [Cons_iff RS iffD1])))]);

qed_goal "Occ_subtree_UN" OccTools.thy
    "Occ_subtree(b, UN z: A. f(z)) = (UN z: A. Occ_subtree(b, f(z)))"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_subtreeI] addSEs [Occ_subtreeE] 
                        addSDs [Cons_iff RS iffD1])))]);

qed_goal "Occ_subtree_Un" OccTools.thy
    "Occ_subtree(b, X Un Y) = Occ_subtree(b, X) Un Occ_subtree(b, Y)"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_subtreeI] addSEs [Occ_subtreeE] 
                        addSDs [Cons_iff RS iffD1])))]);

qed_goal "Occ_subtree_shift" OccTools.thy
    "X <= A*B ==> Occ_subtree(a, Occ_shift(b, X)) = if(a = b, X, 0)"
  (fn [prem] =>
    [(res_inst_tac [("Q", "a = b")] (excluded_middle RS disjE) 1),
     (rtac (if_not_P RS sym RSN (2, trans)) 1),
     (atac 2),
     (rtac (if_P RS sym RSN (2, trans)) 2),
     (atac 3),
     (rtac (subset_empty_iff RS iffD1) 1),
     (rtac subsetI 1),
     (etac notE 1),
     (rtac equalityI 2),
     (rtac subsetI 3),
     (forward_tac [prem RS subsetD] 3),
     (etac SigmaE 3),
     (hyp_subst_tac 3),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_subtreeI, Occ_shiftI] 
                        addSEs [Occ_subtreeE, Occ_shiftE] 
                        addSDs [Cons_iff RS iffD1])))]);

val Occ_subtree_simps = [Occ_subtree_0, Occ_subtree_cons_Nil,
                        Occ_subtree_cons_Cons, Occ_subtree_Un,
                        Occ_subtree_UN, Occ_subtree_shift];

(** Occ_primary **)
qed_goalw "Occ_primaryI" OccTools.thy [Occ_primary_def]
    "<[], T>: X ==> <[], T>: Occ_primary(X)"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac ZF_cs 1)]);

qed_goalw "Occ_primaryE" OccTools.thy [Occ_primary_def]
    "[| x: Occ_primary(X); \
\       !!T. [| x = <[], T>; <[], T>: X |] ==> R |] ==> R"
  (fn major::prems =>
    [(rtac (major RS CollectE) 1),
     (etac exE 1),
     (resolve_tac prems 1),
     (atac 1),
     (hyp_subst_tac 1),
     (atac 1)]);

qed_goal "Occ_primaryE2" OccTools.thy
    "[| <l, T>: Occ_primary(X); \
\       !!T. [| l = []; <[], T>: X |] ==> R |] ==> R"
  (fn major::prems =>
    [(rtac (major RS Occ_primaryE) 1),
     (etac (Pair_iff RS iffD1 RS conjE) 1),
     (resolve_tac prems 1),
     (REPEAT (atac 1))]);

qed_goalw "Occ_primary_0" OccTools.thy [Occ_primary_def]
    "Occ_primary(0) = 0"
  (fn _ =>
    [(fast_tac eq_cs 1)]);

qed_goal "Occ_primary_cons" OccTools.thy
    "Occ_primary(cons(<l, T>, X)) = \
\            if(l = [], cons(<[], T>, Occ_primary(X)), Occ_primary(X))"
  (fn _ =>
    [(res_inst_tac [("Q", "l = []")] (excluded_middle RS disjE) 1),
     (rtac (if_not_P RS sym RSN (2, trans)) 1),
     (atac 2),
     (rtac (if_P RS sym RSN (2, trans)) 2),
     (atac 3),
     (ALLGOALS (rtac equalityI)),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_primaryI] 
                          addSEs [Occ_primaryE])))]);

qed_goal "Occ_primary_continuous" OccTools.thy
    "Occ_primary(Union(X)) = (UN x: X. Occ_primary(x))"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_primaryI] 
                          addSEs [Occ_primaryE])))]);

qed_goal "Occ_primary_UN" OccTools.thy
    "Occ_primary(UN z: X. f(z)) = (UN z: X. Occ_primary(f(z)))"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_primaryI] addSEs [Occ_primaryE])))]);

qed_goal "Occ_primary_Un" OccTools.thy
    "Occ_primary(X Un Y) = Occ_primary(X) Un Occ_primary(Y)"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_primaryI] 
                          addSEs [Occ_primaryE])))]);

qed_goal "Occ_primary_idempotent" OccTools.thy
    "Occ_primary(Occ_primary(X)) = Occ_primary(X)"
  (fn _ =>
    [(rtac equalityI 1),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_primaryI] 
                          addSEs [Occ_primaryE])))]);

qed_goal "Occ_primary_shift" OccTools.thy
    "Occ_primary(Occ_shift(b, X)) = 0"
  (fn _ =>
    [(rtac (subset_empty_iff RS iffD1) 1),
     (ALLGOALS (fast_tac (ZF_cs addSEs list.free_SEs
                        addSEs [Occ_shiftE, Occ_primaryE])))]);

qed_goal "Occ_primary_subtree_shift_eq" OccTools.thy
    "X <= list(A) * B ==> \
\      X = Occ_primary(X) Un (UN z: A. Occ_shift(z, Occ_subtree(z, X)))"
  (fn [prem] =>
    [(rtac equalityI 1),
     (rtac subsetI 1),
     (forward_tac [prem RS subsetD] 1),
     (etac SigmaE 1),
     (hyp_subst_tac 1),
     (etac list.elim 1),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_subtreeI, Occ_shiftI, Occ_primaryI] 
                          addSEs [Occ_subtreeE, Occ_shiftE, Occ_primaryE] 
                          addSDs [Cons_iff RS iffD1])))]);

val Occ_primary_simps = list_free_simps @
    [Occ_primary_0, Occ_primary_cons, 
     Occ_primary_Un, Occ_primary_UN,
     Occ_primary_shift, Occ_primary_idempotent];

(** Occ_cons **)
qed_goalw "Occ_consI1" OccTools.thy [Occ_cons_def]
    "<[], T>: Occ_cons(T, l)"
  (fn prems =>
    [(fast_tac ZF_cs 1)]);

qed_goalw "Occ_consI2" OccTools.thy [Occ_cons_def]
    "[| a: length(l); <m, U>: nth(l, a) |] ==>\
\              <Cons(a, m), U>: Occ_cons(T, l)"
  (fn [a_len, prem] =>
    [(rtac UnI2 1),
     (rtac (a_len RS UN_I) 1),
     (rtac (prem RS Occ_shiftI) 1)]);

qed_goalw "Occ_consE" OccTools.thy [Occ_cons_def]
    "[| x: Occ_cons(T, l); \
\       x = <[], T> ==> R; \
\       !! a m U. [| x = <Cons(a, m), U>; a: length(l); \
\              <m, U>: nth(l, a) |] ==> R \
\    |] ==> R"
  (fn major::prems =>
    [(rtac (major RS UnE) 1),
     (etac singletonE 1),
     (eresolve_tac prems 1),
     (etac UN_E 1),
     (etac Occ_shiftE 1),
     (eresolve_tac prems 1),
     (REPEAT (atac 1))]);

qed_goal "Occ_cons_ConsE" OccTools.thy
    "[| <Cons(a, m), U>: Occ_cons(T, l); \
\       [| a: length(l); <m, U>: nth(l, a) |] ==> R \
\    |] ==> R"
  (fn [major,prem] =>
    [(rtac (major RS Occ_consE) 1),
     (fast_tac (ZF_cs addSEs list.free_SEs) 1),
     (rtac prem 1),
     (ALLGOALS (asm_full_simp_tac (ZF_ss addsimps [Cons_iff])))]);

qed_goalw "Occ_consE2" OccTools.thy [Occ_cons_def]
    "[| x: Occ_cons(T, l); l: list(A); \
\       x = <[], T> ==> R; \
\       !! a m U. [| x = <Cons(a, m), U>; a < length(l); \
\                    <m, U>: nth(l, a) |] ==> R \
\    |] ==> R"
  (fn major::l_list::prems =>
    [(rtac (major RS UnE) 1),
     (etac singletonE 1),
     (eresolve_tac prems 1),
     (etac UN_E 1),
     (etac Occ_shiftE 1),
     (eresolve_tac prems 1),
     (etac (l_list RS length_type RS nat_into_Ord RSN (2, ltI)) 1),
     (atac 1)]);

qed_goal "Occ_cons_type" OccTools.thy
    "[| T: B; l: list(Pow(list(nat)* B)) |] \
\              ==> Occ_cons(T, l) <= list(nat) * B"
  (fn [prem1, prem2] =>
    [(rtac subsetI 1),
     (etac Occ_consE 1),
     (hyp_subst_tac 1),
     (rtac SigmaI 1),
     (resolve_tac list.intrs 1),
     (rtac prem1 1),
     (hyp_subst_tac 1),
     (forward_tac [prem2 RS length_type RSN (2, mem_nat_in_nat)] 1),
     (forward_tac [prem2 RSN (2, nth_type)] 1),
     (asm_full_simp_tac (IFOL_ss addsimps Pow_Un_0_simps) 1),
     (fast_tac (ZF_cs addIs list.intrs) 1)]);

qed_goal "Occ_cons_type2" OccTools.thy
    "[| T: B; length(l): nat; \
\      ALL z: length(l). nth(l, z)<=list(nat)*B |] \
\              ==> Occ_cons(T, l) <= list(nat) * B"
  (fn [prem1, prem2, prem3] =>
    [(rtac subsetI 1),
     (etac Occ_consE 1),
     (hyp_subst_tac 1),
     (rtac SigmaI 1),
     (resolve_tac list.intrs 1),
     (rtac prem1 1),
     (hyp_subst_tac 1),
     (forward_tac [prem2 RSN (2, mem_nat_in_nat)] 1),
     (dtac (prem3 RS bspec) 1),
     (fast_tac (ZF_cs addIs list.intrs) 1)]);

qed_goal "Occ_cons_Nil" OccTools.thy
    "Occ_cons(T, []) = {<[], T>}"
  (fn _ =>
    [(rtac equalityI 1),
     (rtac subsetI 1),
     (etac Occ_consE 1),
     (asm_full_simp_tac (IFOL_ss addsimps [length_Nil]) 2),
     (ALLGOALS (fast_tac (ZF_cs addSIs [Occ_consI1])))]);

qed_goal "Occ_cons_app_last" OccTools.thy
    "l: list(A) ==> Occ_cons(T, l@[X]) = \
\                   Occ_cons(T, l) Un Occ_shift(length(l), X)"
  (fn [l_list] =>
    [(cut_facts_tac [l_list] 1),
     (asm_simp_tac (nth_ss addsimps [Occ_cons_def]) 1)]);

qed_goalw "Occ_subtree_Occ_cons" OccTools.thy [Occ_cons_def]
    "[| b: nat; l: list(Pow(A * B)) |] ==> \
\             Occ_subtree(b, Occ_cons(T, l)) = nth(l, b)"
  (fn [b_nat, l_list] =>
    [(simp_tac (ZF_ss addsimps Occ_subtree_simps) 1),
     (cut_facts_tac [b_nat, l_list] 1),
     (rtac equalityI 1),
     (rtac ([b_nat RS nat_into_Ord,
             l_list RS length_type RS nat_into_Ord] MRS Ord_linear2) 2),
     (safe_tac (ZF_cs addSEs [Occ_subtreeE, Occ_shiftE]
                addSEs list.free_SEs)),
     (asm_full_simp_tac (nth_ss addsimps [nth_over_length_lemma]) 2),
     (rtac UN_I 1),
     (etac ltD 1),
     (forward_tac [nth_type2] 1),
     (atac 1),
     (asm_full_simp_tac (ZF_ss addsimps Occ_subtree_simps
                       addsimps [Pow_iff]) 1)]);

qed_goalw "Occ_primary_Occ_cons" OccTools.thy [Occ_cons_def]
    "Occ_primary(Occ_cons(T, l)) = {<[], T>}"
  (fn _ =>
    [(simp_tac (ZF_ss addsimps Occ_primary_simps
              addsimps [prove_fun "(UN y: A. 0) = 0"]) 1)]);

qed_goal "Occ_cons_iff" OccTools.thy
    "[| l: list(Pow(A * B)); m: list(Pow(A * B)) |] ==> \
     \       Occ_cons(T, l) = Occ_cons(U, m) <-> T = U & \
     \       (ALL n: length(l) Un length(m). nth(l, n) = nth(m, n))"
  (fn [l_list, m_list] =>
    [(safe_tac (ZF_cs addSIs [nat_UnI, length_type])),
     (REPEAT (ares_tac [l_list, m_list] 2)),
     (dres_inst_tac [("f", "Occ_primary")] function_apply_eq 1),
     (asm_full_simp_tac (nth_ss addsimps [Occ_primary_Occ_cons]
                       addsimps [singleton_iff2]) 1),
     (dtac (l_list RS length_type RSN (2, mem_nat_in_nat)) 1),
     (dtac (m_list RS length_type RSN (2, mem_nat_in_nat)) 2),
     (cut_facts_tac [m_list, l_list] 1),
     (dres_inst_tac [("f", "Occ_subtree(n)")] function_apply_eq 1),
     (asm_full_simp_tac (nth_ss addsimps [Occ_subtree_Occ_cons]) 1),
     (cut_facts_tac [m_list, l_list] 1),
     (dres_inst_tac [("f", "Occ_subtree(n)")] function_apply_eq 1),
     (asm_full_simp_tac (nth_ss addsimps [Occ_subtree_Occ_cons]) 1),
     (rewrite_goals_tac [Occ_cons_def]),
     (rtac equalityI 1),
     (safe_tac ZF_cs),
     (ALLGOALS (forward_tac ([l_list, m_list] RL [length_type]
                             RLN (2, [mem_nat_in_nat])))),
     (ALLGOALS (cut_facts_tac [l_list, m_list])),
     (excluded_middle_tac "z < length(l)" 2),
     (dtac not_lt_imp_le 2),
     (etac (m_list RS length_type 
            RSN (2, mem_nat_in_nat) RS nat_into_Ord) 2),
     (rtac (l_list RS length_type RS nat_into_Ord) 2),
     (excluded_middle_tac "z < length(m)" 1),
     (dtac not_lt_imp_le 1),
     (etac (l_list RS length_type 
            RSN (2, mem_nat_in_nat) RS nat_into_Ord) 1),
     (rtac (m_list RS length_type RS nat_into_Ord) 1),
     (ALLGOALS ((dtac bspec) THEN' (eresolve_tac [UnI1,UnI2]))),
     (dtac sym 3),
     (dtac sym 4),
     (ALLGOALS (rotate_tac 4)),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps [Occ_shift_0,
                                                    nth_over_length_lemma]))),
     (ALLGOALS ((swap_res_tac [UN_I]) THEN' (etac ltD) THEN' atac))]);

val Occ_cons_simps = [nat_succ_Un, Occ_cons_iff,
                      Occ_subtree_Occ_cons, Occ_primary_Occ_cons];

(** functional **)
qed_goalw "functionalI" OccTools.thy [functional_def]
    "[| !!l A B. [| <l, A>: X; <l, B>: X |] ==> A = B |] ==> functional(X)"
  (fn prems =>
    [(REPEAT (resolve_tac [allI, impI] 1)),
     (etac conjE 1),
     (REPEAT (ares_tac prems 1))]);

qed_goalw "functionalD" OccTools.thy [functional_def]
    "[| functional(X); <l, A>: X; <l, B>: X |] ==> A = B"
  (fn major::prems =>
    [(rtac (prems MRS (conjI RS 
                       (major RS spec RS spec RS spec RS mp))) 1)]);


(** DenseTree **)
qed_goalw "DenseTreeI" OccTools.thy [DenseTree_def]
    "[| !!l A m. [| <l, A>: X; initseg(nat, m, l) |] ==> (EX B. <m, B>: X) |]\
\       ==> DenseTree(X)"
  (fn prems =>
    [(REPEAT (resolve_tac [allI, impI] 1)),
     (etac conjE 1),
     (REPEAT (ares_tac prems 1))]);

qed_goalw "DenseTreeE" OccTools.thy [DenseTree_def]
    "[| DenseTree(X); \
\       <l, A>: X; initseg(nat, m, l);\
\       !!B. [| <m, B>: X |] ==> R |] ==> R"
  (fn major::prems =>
    [(rtac (conjI RS (major RS spec RS spec RS spec RS mp RS exE)) 1),
     (REPEAT (ares_tac prems 1))]);

(** CorrectArity **)
qed_goalw "CorrectArityI" OccTools.thy [CorrectArity_def]
    "[| !!l m. [| <l, T>: X; m < n |] ==> (EX N. <l @ [m], N> : X); \
\       !!l m. [| <l, T>: X; n le m; (EX N. <l @ [m], N> : X) |] ==> False\
\    |] ==> CorrectArity(X, T, n)"
  (fn prems =>
    [(REPEAT (resolve_tac [allI, impI, conjI] 1)),
     (REPEAT (resolve_tac [allI, impI, notI] 2)),
     (REPEAT (ares_tac prems 1))]);

qed_goalw "CorrectArityD1" OccTools.thy [CorrectArity_def]
    "[| CorrectArity(X, T, n); \
\      <l, T>: X; m < n |] ==>  (EX N. <l @ [m], N>: X)"
  (fn major::prems =>
    [(rtac (major RS spec RS mp RS conjunct1 RS spec RS mp) 1),
     (REPEAT (ares_tac prems 1))]);

qed_goalw "CorrectArityD2" OccTools.thy [CorrectArity_def]
    "[| CorrectArity(X, T, n); \
\      <l, T>: X; n le m |] ==> ~(EX N. <l @ [m], N>: X)"
  (fn major::prems =>
    [(rtac (major RS spec RS mp RS conjunct2 RS spec RS mp) 1),
     (REPEAT (ares_tac prems 1))]);

qed_goal "CorrectArityE" OccTools.thy
    "[| CorrectArity(X, T, n); \
\       !!N. [| m < n; <l @ [m], N>: X |] ==> R; \
\       n le m ==> EX N. <l @ [m], N>: X; \
\       <l, T>: X; m: nat; n: nat |] ==> R"
  (fn major::case1::case2::prems =>
    [(rtac Ord_linear2 1),
     (forward_tac [case2] 4),
     (rtac (major RS CorrectArityD2 RS notE) 4),
     (rtac (major RS CorrectArityD1 RS exE) 3),
     (rtac case1 5),
     (REPEAT (ares_tac (prems @ [nat_into_Ord]) 1))]);

(** Occ_range **)
qed_goalw "Occ_rangeE" OccTools.thy [Occ_range_def]
    "[| X: Occ_range(Tag, Arity); \
\       [| X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); \
\          X ~= 0; functional(X); DenseTree(X); \
\          ALL T: Tag. CorrectArity(X, T, Arity(T)) |] ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(rtac (major RS CollectE) 1),
     (REPEAT (etac conjE 1)),
     (rtac prem 1),
     (REPEAT (atac 1))]);

qed_goalw "Occ_rangeI" OccTools.thy [Occ_range_def]
    "[| X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); \
\       X ~= 0; functional(X); DenseTree(X); \
\       ALL T: Tag. CorrectArity(X, T, Arity(T))\
\    |] ==> X: Occ_range(Tag, Arity)"
  (fn prems =>
    [(rtac CollectI 1),
     (REPEAT (ares_tac ([conjI] @ prems) 1))]);

qed_goal "Occ_range_functionalD" OccTools.thy
    "X: Occ_range(Tag, Arity) ==> functional(X)"
  (fn [major] =>
    [(rtac (major RS Occ_rangeE) 1),
     (atac 1)]);

qed_goal "Occ_range_DenseTreeD" OccTools.thy
    "X: Occ_range(Tag, Arity) ==> DenseTree(X)"
  (fn [major] =>
    [(rtac (major RS Occ_rangeE) 1),
     (atac 1)]);

qed_goal "Occ_range_CorrectArityD" OccTools.thy
    "[| X: Occ_range(Tag, Arity); T: Tag |] \
\         ==> CorrectArity(X, T, Arity(T))"
  (fn [major, prem] =>
    [(rtac (major RS Occ_rangeE) 1),
     (etac (prem RSN (2, bspec)) 1)]);


(** Occ_cons_cond **)
qed_goalw "Occ_cons_condD1" OccTools.thy [Occ_cons_cond_def]
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); T: Tag |] ==> Arity(T): nat"
  (fn [major, prem] =>
    [(rtac (prem RS ((major RS conjunct1) RS bspec)) 1)]);

qed_goalw "Occ_cons_condD2" OccTools.thy [Occ_cons_cond_def]
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       T: Tag; l: list(Pow(list(nat) * Tag)); \
\       Arity(T) = length(l); \
\       ALL z: length(l). EX N: Terms. nth(l, z) = Occ(N) \
\    |] ==> EX M: Terms. Occ(M) = Occ_cons(T, l)"
  (fn major::prems =>
    [(rtac (major RS conjunct2 RS bspec RS bspec RS mp) 1),
     (REPEAT (ares_tac ([conjI] @ prems) 1))]);

qed_goalw "Occ_cons_condI" OccTools.thy [Occ_cons_cond_def]
    "[| !!T. T: Tag ==> Arity(T): nat;\
\       !!T l. [| T: Tag; l: list(Pow(list(nat) * Tag)); \
\          length(l) = Arity(T); \
\          ALL z: length(l). EX N: Terms. nth(l, z) = Occ(N) |] \
\          ==> EX M: Terms. Occ(M) = Occ_cons(T, l) \
\    |] ==> Occ_cons_cond(Terms, Occ, Tag, Arity)"
  (fn [prem1, prem2] =>
    [(rtac conjI 1),
     (rtac ballI 1),
     (REPEAT (rtac ballI 2)),
     (rtac impI 2),
     (etac prem1 1),
     (REPEAT (etac conjE 1)),
     (rtac prem2 1),
     (etac sym 3),
     (REPEAT (atac 1))]);

(** Occ_ind_cond **)
qed_goalw "Occ_ind_condD" OccTools.thy [Occ_ind_cond_def]
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       M: Terms; \
\       !! l T. [| T: Tag; l: list(Terms); \
\             Term_cons(T, l): Terms; \
\             Arity(T) = length(l); \
\             Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l)); \
\             ALL z: length(l). P(nth(l, z)) |]  ==> P(Term_cons(T, l)) \
\    |] ==> P(M)"
  (fn [major, prem, indstep] =>
    [(res_inst_tac [("A", "Terms")] CollectD2 1),
     (rtac (major RS spec RS mp RS bspec) 1),
     (rtac prem 2),
     (REPEAT (resolve_tac [impI, ballI, allI] 1)),
     (REPEAT (etac conjE 1)),
     (rtac CollectI 1),
     (atac 1),
     (etac indstep 1),
     (rtac ballI 5),
     (dtac bspec 5),
     (atac 5),
     (etac CollectE 5),
     (REPEAT (atac 1))]);

qed_goalw "Occ_ind_condI" OccTools.thy [Occ_ind_cond_def]
    "[| !!P M. [| M: Terms; \
\            ALL T: Tag. ALL l: list(Terms). \
\               Term_cons(T, l): Terms & \
\               Arity(T) = length(l) & \
\               Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l)) &\
\               (ALL z: length(l). P(nth(l, z))) --> P(Term_cons(T, l)) \
\            |] ==> P(M) \
\    |] ==> Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  (fn [ind] =>
    [(rtac allI 1),
     (rtac impI 1),
     (rtac ballI 1),
     (eres_inst_tac [("P", "%x. x: P")] ind 1),
     (atac 1)]);

qed_goal "Occ_ind_cond_Occ_domain" OccTools.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); M: Terms |] ==> \
\        Occ(M) <= list(nat) * Tag"
  (fn [major, prem] =>
    [(rtac ([major, prem] MRS Occ_ind_condD) 1),
     (eres_inst_tac [("P", "%x. x <= ?X")] ssubst 1),
     (rtac Occ_cons_type2 1),
     (atac 1),
     (asm_simp_tac nth_ss 1),
     (asm_simp_tac (nth_ss addsimps [nth_map, length_map]) 1)]);

qed_goal "Occ_ind_cond_Occ_induct" OccTools.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); M: Terms; \
\       !! l T. [| T: Tag; l: list(Pow(list(nat) * Tag)); \
\             Occ_cons(T, l) <= list(nat) * Tag; \
\             length(l) = Arity(T); \
\             ALL z: length(l). P(nth(l, z)) |]  ==> P(Occ_cons(T, l)) \
\    |] ==> P(Occ(M))"
  (fn [major, prem, indstep] =>
    [(rtac ([major, prem] MRS Occ_ind_condD) 1),
     (asm_simp_tac IFOL_ss 1),
     (rtac indstep 1),
     (atac 1),
     (eres_inst_tac [("P", "%x. x <= ?X")] subst 2),
     (etac (major RS Occ_ind_cond_Occ_domain) 2),
     (rtac map_type 1),
     (etac (major RS Occ_ind_cond_Occ_domain RS PowI) 2),
     (atac 1),
     (REPEAT (CHANGED (asm_simp_tac 
                       (nth_ss addsimps [length_map, nth_map]) 1)))]);

val Occ_ind_cond_Occ_inj_lemma = prove_goal OccTools.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); M: Terms |] ==> \
\       ALL N: Terms. Occ(M) = Occ(N) --> M = N"
  (fn [major, prem] =>
    [(rtac ([major, prem] MRS Occ_ind_condD) 1),
     (rtac ballI 1),
     (eres_inst_tac [("M", "N")] (major RS Occ_ind_condD) 1),
     (asm_simp_tac IFOL_ss 1),
     (rtac impI 1),
     (rtac (make_elim(Occ_cons_iff RS iffD1)) 1),
     (atac 3),
     (REPEAT ((rtac map_type 1) THEN
            (atac 1) THEN
            (etac (major RS Occ_ind_cond_Occ_domain RS PowI) 1))),
     (etac conjE 1),
     (hyp_subst_tac 1),
     (asm_full_simp_tac (IFOL_ss addsimps [length_map, Un_absorb]) 1),
     (res_inst_tac [("a", "la"), ("b", "l")] ssubst 1),
     (rtac refl 2),
     (rtac nth_inj 1),
     (REPEAT (atac 2)),
     (asm_full_simp_tac (nth_ss addsimps [nth_map]) 1),
     (rtac ballI 1),
     (etac (bspec RS bspec RS mp) 1),
     (dtac (length_type RSN (2, nat_ltI)) 2),
     (ALLGOALS (asm_simp_tac nth_ss))]);

qed_goal "Occ_ind_cond_Occ_inj" OccTools.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       M: Terms; N: Terms |] ==> Occ(M) = Occ(N) <-> M = N"
  (fn major::prems =>
    [(rtac iffI 1),
     (rtac (major RS Occ_ind_cond_Occ_inj_lemma RS bspec RS mp) 1),
     (etac subst 4),
     (REPEAT (ares_tac ([refl] @ prems) 1))]);

(** Monotonisity **)
qed_goal "Occ_shift_mono" OccTools.thy
    "X <= Y ==> Occ_shift(b, X) <= Occ_shift(b, X)"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac (ZF_cs addSEs [Occ_shiftE] addSIs [Occ_shiftI]) 1)]);

qed_goal "Occ_subtree_mono" OccTools.thy
    "X <= Y ==> Occ_subtree(b, X) <= Occ_subtree(b, X)"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac (ZF_cs addSEs [Occ_subtreeE] addSIs [Occ_subtreeI]) 1)]);

qed_goal "Occ_primary_mono" OccTools.thy
    "X <= Y ==> Occ_primary(X) <= Occ_primary(X)"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac (ZF_cs addSEs [Occ_primaryE] addSIs [Occ_primaryI]) 1)]);

(** Finiteness **)
qed_goal "Occ_shift_FinI" OccTools.thy
    "[| X: Fin(list(A)*B); b: A |] ==>  Occ_shift(b, X): Fin(list(A)*B)"
  (fn [major, prem] =>
    [(rtac (major RS Fin_induct) 1),
     (etac SigmaE 2),
     (hyp_subst_tac 2),
     (ALLGOALS (simp_tac (nth_ss addsimps Occ_shift_simps))),
     (ALLGOALS (resolve_tac Fin.intrs)),
     (cut_facts_tac [prem] 1),
     (asm_simp_tac list_ss 1),
     (atac 1)]);

qed_goal "Occ_subtree_FinI" OccTools.thy
    "X: Fin(list(A)*B) ==>  Occ_subtree(b, X): Fin(list(A)*B)"
  (fn [major] =>
    [(rtac (major RS Fin_induct) 1),
     (etac SigmaE 2),
     (etac list.elim 2),
     (ALLGOALS (asm_simp_tac (nth_ss addsimps Occ_subtree_simps))),
     (rtac if_type 2),
     (atac 3),
     (ALLGOALS (resolve_tac Fin.intrs)),
     (asm_simp_tac list_ss 1),
     (hyp_subst_tac 1),
     (atac 1)]);

qed_goal "Occ_primary_FinI" OccTools.thy
    "X: Fin(list(A)*B) ==>  Occ_primary(X): Fin(list(A)*B)"
  (fn [major] =>
    [(rtac (major RS Fin_induct) 1),
     (etac SigmaE 2),
     (etac list.elim 2),
     (ALLGOALS (asm_simp_tac (nth_ss addsimps Occ_primary_simps))),
     (ALLGOALS (resolve_tac Fin.intrs)),
     (asm_simp_tac list_ss 1),
     (atac 1)]);

qed_goal "Occ_cons_FinI" OccTools.thy
    "[| l: list(Fin(list(nat)*Tag)); T: Tag |] ==> \
\                   Occ_cons(T, l): Fin(list(nat)*Tag)"
  (fn [major, prem] =>
    [(rtac (major RS list_append_induct) 1),
     (ALLGOALS (asm_simp_tac (nth_ss addsimps [Occ_cons_Nil,
                                             Occ_cons_app_last]))),
     (cut_facts_tac [prem] 1),
     (fast_tac (ZF_cs addIs list.intrs addIs Fin.intrs) 1),
     (fast_tac (ZF_cs addIs [length_type, Occ_shift_FinI, Fin_UnI]) 1)]);

(** Occ_fbs_op **)
qed_goalw "Occ_fbs_op_continuous" OccTools.thy [Occ_fbs_op_def]
    "X ~= 0 ==> Occ_fbs_op(Tag, Union(X)) = (UN x: X. Occ_fbs_op(Tag, x))"
  (fn [prem] =>
    [(subgoals_tac ["{domain(x). x: X} ~= 0"] 1),
     (asm_simp_tac (list_ss addsimps continuous_simps
                  addsimps [list_op_continuous]) 1),
     (cut_facts_tac [prem] 1),
     (etac not_emptyE 1),
     (rtac not_emptyI 1),
     (rtac RepFunI 1),
     (atac 1)]);

qed_goalw "Occ_fbs_mono_inj_pair" OccTools.thy [Occ_fbs_dom_def]
    "[| X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); \
\       X ~= 0 |] ==> mono_inj_pair(list_dom(nat), %x. x * Tag , domain)"
  (fn [prem1, prem2] =>
    [(rtac (prem2 RS not_emptyE) 1),
     (dtac ((prem1 RS (fin_bnd_set_domain RS subsetD) RS PowD) RS subsetD) 1),
     (etac SigmaE 1),
     (etac Prod_domain_mono_inj_pair 1)]);

qed_goalw "Occ_fbs_mono_inj_pair2" OccTools.thy [Occ_fbs_dom_def]
    "[| X <= A * Tag; \
\       X ~= 0 |] ==> mono_inj_pair(list_dom(nat), %x. x * Tag , domain)"
  (fn [prem1, prem2] =>
    [(rtac (prem2 RS not_emptyE) 1),
     (dtac (prem1 RS subsetD) 1),
     (etac SigmaE 1),
     (etac Prod_domain_mono_inj_pair 1)]);

qed_goal "Occ_fbs_op_bnd_cont" OccTools.thy
    "bnd_cont(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  (fn _ =>
    [(rtac bnd_contI 1),
     (etac Occ_fbs_op_continuous 1),
     (rewrite_goals_tac [Occ_fbs_op_def, Occ_fbs_dom_def]),
     (res_inst_tac [("Q", "Tag = 0")] (excluded_middle RS disjE) 1),
     (etac not_emptyE 1),
     (asm_simp_tac (ZF_ss addsimps [domain_of_prod]) 1),
     (cut_facts_tac [list_op_bnd_mono RS bnd_monoD1] 1),
     (fast_tac ZF_cs 1),
     (hyp_subst_tac 1),
     (asm_simp_tac ZF_ss 1)]);

val Occ_fbs_op_bnd_mono = Occ_fbs_op_bnd_cont RS bnd_cont_bnd_mono;

qed_goal "Occ_fbs_op_lfp_eq" OccTools.thy
    "lfp(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)) = list(nat) * Tag"
  (fn _ =>
    [(res_inst_tac [("Q", "Tag = 0")] (excluded_middle RS disjE) 1),
     (etac not_emptyE 1),
     (dres_inst_tac [("A1", "nat")] ([Prod_domain_mono_inj_pair, 
                                   list_op_bnd_mono]
                                  MRS mono_inj_pair_lfp_eq) 1),
     (fold_goals_tac [Occ_fbs_dom_def, Occ_fbs_op_def]),
     (etac (list_op_lfp_eq RS ssubst) 1),
     (hyp_subst_tac 1),
     (simp_tac (ZF_ss addsimps [Occ_fbs_dom_def, lfp_def, 
                              Occ_fbs_op_def, 
                              prove_fun "Pow(0) = {0}"]) 1)]);

qed_goal "Occ_fbs_op_fin_bnd_set_upper_Fin" OccTools.thy
    "Fin(list(nat) * Tag) <= fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  (fn _ =>
    [(cut_facts_tac [Occ_fbs_op_bnd_cont RS fin_bnd_set_upper_Fin_lfp] 1),
     (etac (Occ_fbs_op_lfp_eq RS subst) 1)]);

qed_goal "Occ_fbs_op_lfp_lowerbound" OccTools.thy
    "X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)) \
\      ==> X <= list(nat) * Tag"
  (fn prems =>
    [(rtac (Occ_fbs_op_lfp_eq RS subst) 1),
     (rtac (Occ_fbs_op_bnd_mono RS 
          fin_bnd_set_Pow_lfp_lowerbound RS subsetD RS PowD) 1),
     (resolve_tac prems 1)]);

(** Preservation Properties of Occ_subtree **)
qed_goal "Occ_subtree_preserves_domain" OccTools.thy
    "X <= list(A) * B ==> Occ_subtree(b, X) <= list(A) * B"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (fast_tac (ZF_cs addSEs [Occ_subtreeE, ConsE]) 1)]);

qed_goal "Occ_subtree_preserves_functionality" OccTools.thy
    "functional(X) ==> functional(Occ_subtree(a, X))"
  (fn [prem] =>
    [(rtac functionalI 1),
     (REPEAT (dtac Occ_subtreeD 1)),
     (etac (prem RS functionalD) 1),
     (atac 1)]);

qed_goal "Occ_subtree_preserves_CorrectArity" OccTools.thy
    "CorrectArity(X, T, n) ==> CorrectArity(Occ_subtree(a, X), T, n)"
  (fn [prem] =>
    [(rtac CorrectArityI 1),
     (ALLGOALS (etac Occ_subtreeE2)),
     (dtac (prem RS CorrectArityD2) 2),
     (dtac (prem RS CorrectArityD1) 1),
     (TRYALL atac),
     (etac notE 2),
     (ALLGOALS (etac exE)),
     (dtac Occ_subtreeD 2),
     (ALLGOALS (rtac exI)),
     (rtac Occ_subtreeI 1),
     (ALLGOALS (asm_full_simp_tac list_ss))]);

qed_goal "Occ_subtree_preserves_DenseTree" OccTools.thy
    "[| DenseTree(X); a: nat |] ==> DenseTree(Occ_subtree(a, X))"
  (fn [prem, a_nat] =>
    [(rtac DenseTreeI 1),
     (dtac Occ_subtreeD 1),
     (etac (prem RS DenseTreeE) 1),
     (rtac initseg_ConsI 1),
     (atac 2),
     (rtac exI 2),
     (etac Occ_subtreeI 2),
     (rtac a_nat 1)]);

qed_goal "Occ_subtree_preserves_not_empty" OccTools.thy
    "[| <[], T>: X; CorrectArity(X, T, n); n: nat |] ==>\
\         ALL z: n. Occ_subtree(z, X) ~= 0"
  (fn [major, prem, n_nat] =>
    [(rtac ballI 1),
     (forward_tac [n_nat RS nat_into_Ord RSN (2, ltI)] 1),
     (dtac ([prem, major] MRS CorrectArityD1) 1),
     (etac exE 1),
     (rtac not_emptyI 1),
     (rtac Occ_subtreeI 1),
     (asm_full_simp_tac list_ss 1)]);

qed_goalw "Occ_subtree_Occ_fbs_op_lemma" OccTools.thy
                                     [Occ_fbs_op_def, list_op_def]
    "x <= Occ_fbs_op(Tag, Z) ==> Occ_subtree(b, x) <= domain(Z) * Tag"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (fast_tac (ZF_cs addSEs [Occ_subtreeE] 
              addSEs list.free_SEs
              addSDs [Cons_iff RS iffD1]) 1)]);

qed_goal "Occ_subtree_in_fin_bnd_set" OccTools.thy
    "[| X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); X ~= 0 |] \
\      ==> Occ_subtree(b, X): fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  (fn [prem1, prem2] =>
    [(rtac (prem1 RS (Occ_fbs_op_bnd_mono RS fin_bnd_set_boundE)) 1),
     (rtac (Occ_fbs_op_bnd_mono RS fin_bnd_set_subsetI) 1),
     (rtac Occ_subtree_Occ_fbs_op_lemma 1),
     (etac subset_trans 1),
     (atac 1),
     (rtac (Occ_fbs_op_bnd_mono RS fin_bnd_setI2) 1),
     (etac fin_bnd_setE 1),
     (rewrite_goals_tac [fin_bnd_def, Occ_fbs_op_def]),
     (etac (rewrite_rule [fin_bnd_def] ([[prem1, prem2] MRS 
                                       Occ_fbs_mono_inj_pair, 
                                       list_op_bnd_mono] MRS
                                      mono_inj_pair_fin_bnd_lemma)) 1)]);

qed_goal "Occ_subtree_in_Occ_range" OccTools.thy
    "[| <Cons(a, l), T>: X; X: Occ_range(Tag, Arity); a: nat |] \
\          ==> Occ_subtree(a, X): Occ_range(Tag, Arity)"
  (fn [major, prem, a_nat] =>
    [(rtac Occ_rangeI 1),
     (rtac ballI 5),
     (rtac not_emptyI 2),
     (rtac (major RS Occ_subtreeI) 2),
     (ALLGOALS (rtac (prem RS Occ_rangeE))),
     (ALLGOALS (resolve_tac [Occ_subtree_in_fin_bnd_set,
                           Occ_subtree_preserves_functionality,
                           Occ_subtree_preserves_DenseTree,
                           Occ_subtree_preserves_CorrectArity])),
     (etac bspec 6),
     (REPEAT (ares_tac [a_nat] 1))]);

(** Range of Occurence  **)
qed_goal "Occ_domain_lemma" OccTools.thy
    "[| X <= Occ_fbs_dom(Tag); \
\       mono_inj_pair(list_dom(nat), %x. x * Tag , domain); \
\       bnd_mono(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); \
\       Z: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); \
\       X <= Occ_fbs_op(Tag, Z) |] ==> X <= list(nat)*Tag"
  (fn major::hinj::hmono::prems =>
    [(rtac (list_op_lfp_eq RS ssubst) 1),
     (rtac (rewrite_rule [Occ_fbs_dom_def] 
            ([hinj, list_op_bnd_mono] MRS 
             mono_inj_pair_lfp_eq RS subst)) 1),
     (fold_goals_tac [Occ_fbs_dom_def, Occ_fbs_op_def]),
     (rtac (hmono RS fin_bnd_set_Pow_lfp_lowerbound RS subsetD RS PowD) 1),
     (resolve_tac (prems RL [fin_bnd_setE]) 1),
     (rtac (major RS fin_bnd_setI) 1),
     (rtac (hmono RS fin_bnd_succ) 1),
     (REPEAT (ares_tac prems 1))]);

qed_goal "Occ_DenseTree_not_empty_lemma" OccTools.thy
    "[| X ~= 0; X <= list(nat) * Tag; DenseTree(X) |] ==> \
\        EX N: Tag. <[], N>: X"
  (fn [major, domX, hierX] =>
    [(rtac (major RS not_emptyE) 1),
     (forward_tac [domX RS subsetD] 1),
     (etac SigmaE 1),
     (hyp_subst_tac 1),
     (etac (hierX RS DenseTreeE) 1),
     (etac (initseg_NilI) 1),
     (forward_tac [domX RS subsetD] 1),
     (etac SigmaE2 1),
     (etac bexI 1),
     (atac 1)]);

qed_goal "Occ_primary_functional_lemma" OccTools.thy
    "[| <[], T>: X; functional(X) |] ==> Occ_primary(X) = {<[], T>}"
  (fn [major, funcX] =>
    [(rtac equalityI 1),
     (rtac subsetI 1),
     (etac Occ_primaryE 1),
     (dtac (major RS (funcX RS functionalD)) 1),
     (hyp_subst_tac 1),
     (rtac singletonI 1),
     (rtac subsetI 1),
     (etac singletonE 1),
     (hyp_subst_tac 1),
     (rtac (major RS Occ_primaryI) 1)]);

qed_goal "Occ_range_lemma1" OccTools.thy
    "[| Arity(T): nat; \
\       ALL z: Arity(T). Occ_subtree(z, X) ~= 0; \
\       ALL y. y <= domain(Z)*Tag --> \
\              y ~=0 & functional(y) & DenseTree(y) & \
\              (ALL T: Tag. CorrectArity(y, T, Arity(T))) --> \
\                      (EX M: Terms. y = Occ(M)); \
\       X <= Occ_fbs_op(Tag, Z); \ 
\       functional(X); DenseTree(X); \
\       ALL T:Tag. CorrectArity(X, T, Arity(T)) \
\    |] ==> ALL z: Arity(T). EX N: Terms. Occ_subtree(z, X) = Occ(N)"
  (fn [Arity_nat, not_empty, prem1, prem2, funcX, hierX, 
     corrX] =>
    [(rtac ballI 1),
     (cut_facts_tac [(prem2 RS Occ_subtree_Occ_fbs_op_lemma) RS
                   (prem1 RS spec RS mp)] 1),
     (etac mp 1),
     (forward_tac [Arity_nat RSN (2, mem_nat_in_nat)] 1),
     (REPEAT (ares_tac [conjI, ballI, funcX, hierX, corrX RS bspec,
                      not_empty RS bspec,
                      Occ_subtree_preserves_functionality,
                      Occ_subtree_preserves_DenseTree,
                      Occ_subtree_preserves_CorrectArity] 1))]);

qed_goal "Occ_range_lemma2" OccTools.thy
    "[|Arity(T): nat; X <= list(nat)*Tag; \
\      ALL z: Arity(T). EX N: Terms. Occ_subtree(z, X) = Occ(N)\
\    |] ==> EX l: list(Pow(list(nat)*Tag)). Arity(T) = length(l) &\
\             (ALL z: length(l). nth(l, z) = Occ_subtree(z, X)) &\
\             (ALL z: length(l). EX N: Terms. nth(l, z) = Occ(N))"
  (fn [Arity_nat, domX, prem] =>
    [(rtac (make_elim nth_existence_lemma) 1),
     (rtac Arity_nat 2),
     (rtac ballI 1),
     (res_inst_tac [("b1", "z")] 
      (domX RS Occ_subtree_preserves_domain RS PowI) 1),
     (etac bexE 1),
     (etac conjE 1),
     (rtac bexI 1),
     (atac 2),
     (rtac conjI 1),
     (etac sym 1),
     (rtac conjI 1),
     (etac ssubst 1),
     (atac 1),
     (rtac ballI 1),
     (asm_full_simp_tac IFOL_ss 1),
     (forward_tac [prem RS bspec] 1),
     (etac bexE 1),
     (rtac bexI 1),
     (rtac trans 1),
     (etac bspec 1),
     (REPEAT (atac 1))]);

qed_goal "Occ_cons_lemma" OccTools.thy
    "[| <[], T>: X; CorrectArity(X, T, length(l)); \
\       functional(X); DenseTree(X); \
\       X <= list(nat) * Tag; l: list(A); \
\       ALL z: length(l). nth(l, z) = Occ_subtree(z, X) \
\    |] ==> Occ_cons(T, l) = X"
  (fn [major, crrX, funcX, hierX, domX, l_list, prem] =>
    [(rtac sym 1),
     (rtac (domX RS Occ_primary_subtree_shift_eq RS trans) 1),
     (simp_tac (IFOL_ss addsimps [[major, funcX] MRS 
                                Occ_primary_functional_lemma]) 1),
     (rtac equalityI 1),
     (rtac subsetI 1),
     (etac UnE 1),
     (etac singletonE 1),
     (hyp_subst_tac 1),
     (rtac Occ_consI1 1),
     (etac UN_E 1),
     (etac Occ_shiftE 1),
     (hyp_subst_tac 1),
     (rtac (crrX RS CorrectArityE) 1),
     (rtac major 3),
     (atac 3),
     (rtac (l_list RS length_type) 3),
     (rtac Occ_consI2 1),
     (etac ltD 1),
     (dtac ltD 1),
     (dtac (prem RS bspec) 1),
     (etac ssubst 1),
     (atac 1),
     (dtac Occ_subtreeD 1),
     (rtac (hierX RS DenseTreeE) 1),
     (atac 1),
     (etac initseg_ConsI 1),
     (rtac initseg_NilI 1),
     (dtac (domX RS subsetD) 1),
     (etac SigmaE2 1),
     (etac ConsE 1),
     (atac 1),
     (rtac exI 1),
     (asm_simp_tac list_ss 1),
     (rtac subsetI 1),
     (etac Occ_consE 1),
     (fast_tac ZF_cs 1),
     (hyp_subst_tac 1),
     (rtac UnI2 1),
     (rtac UN_I 1),
     (rtac Occ_shiftI 2),
     (etac (l_list RS length_type RSN (2, mem_nat_in_nat)) 1),
     (dtac (prem RS bspec) 1),
     (etac subst 1),
     (atac 1)]);

qed_goal "Occ_fbs_op_fin_bnd_induct" OccTools.thy
    "[| X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); X ~= 0; \
\       !!X. [| X <= list(nat)*Tag; X ~= 0; \
\               EX Z: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)). \
\                 X <= Occ_fbs_op(Tag, Z) & \
\             (ALL Y. Y <= domain(Z)*Tag --> Y ~= 0 -->P(Y)) |] ==> P(X) \
\    |] ==> P(X)"
  (fn [major, prem, indstep] =>
    [(rtac (prem RS rev_mp) 1),
     (res_inst_tac [("a", "X")] mono_inj_pair_fin_bnd_set_induct 1),
     (rtac ([major, prem]  MRS Occ_fbs_mono_inj_pair) 1),
     (rtac trivial_mono_inj_pair 1),
     (rtac Prod_domain_0_eq 1),
     (rtac list_op_bnd_mono 1),
     (fold_goals_tac [Occ_fbs_dom_def, Occ_fbs_op_def]),
     (rtac major 1),
     (fast_tac ZF_cs 1),
     (rtac impI 1),
     (etac bexE 1),
     (REPEAT (etac conjE 1)),
     (dtac Occ_domain_lemma 1),
     (REPEAT (ares_tac [[major, prem] MRS
                      Occ_fbs_mono_inj_pair, Occ_fbs_op_bnd_mono] 1)),
     (rtac indstep 1),
     (REPEAT (ares_tac [bexI, conjI] 1))]);

qed_goalw "Occ_range_existence_lemma" OccTools.thy [Occ_range_def]
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       X: Occ_range(Tag, Arity) |] ==> EX M: Terms. X = Occ(M)"
  (fn [major, prem] =>
    [(rtac (prem RS CollectD2 RS rev_mp) 1),
     (res_inst_tac [("a", "X")] mono_inj_pair_fin_bnd_set_induct 1),
     (rtac Occ_fbs_mono_inj_pair 1),
     (rtac (prem RS CollectD1) 1),
     (rtac (prem RS CollectD2 RS conjunct1) 1),
     (rtac trivial_mono_inj_pair 1),
     (rtac Prod_domain_0_eq 1),
     (rtac list_op_bnd_mono 1),
     (fold_goals_tac [Occ_fbs_dom_def, Occ_fbs_op_def]),
     (rtac (prem RS CollectD1) 1),
     (fast_tac ZF_cs 1),
     (etac bexE 1),
     (rtac impI 1),
     (REPEAT (etac conjE 1)),
     (dtac Occ_domain_lemma 1),
     (rtac Occ_fbs_op_bnd_mono 2),
     (rtac Occ_fbs_mono_inj_pair 1),
     (rtac (prem RS CollectD1) 1),
     (REPEAT (ares_tac [prem RS CollectD2 RS conjunct1] 1)),
     (forward_tac [Occ_DenseTree_not_empty_lemma] 1),
     (REPEAT (atac 1)),
     (etac bexE 1),
     (forward_tac [bspec] 1),
     (atac 1),
     (forward_tac [major RS Occ_cons_condD1] 1),
     (forward_tac [Occ_subtree_preserves_not_empty] 1),
     (REPEAT (atac 1)),
     (forw_inst_tac [("Arity", "Arity")] Occ_range_lemma1 1),
     (REPEAT (atac 1)),
     (forw_inst_tac [("Arity", "Arity")] Occ_range_lemma2 1),
     (REPEAT (atac 1)),
     (etac bexE 1),
     (REPEAT (etac conjE 1)),
     (forward_tac [major RS Occ_cons_condD2] 1),
     (REPEAT (atac 1)),
     (etac bexE 1),
     (forw_inst_tac [("l", "l")] Occ_cons_lemma 1),
     (eres_inst_tac [("P", "%x. CorrectArity(?X, ?T, x)")] subst 1),
     (REPEAT (atac 1)),
     (rtac bexI 1),
     (etac (sym RS trans) 1),
     (etac sym 1),
     (atac 1)]);

qed_goalw "Occ_range_depth_induct" OccTools.thy [Occ_range_def]
    "[| X: Occ_range(Tag, Arity); \
\       !!X. [| X <= list(nat) * Tag; X: Occ_range(Tag, Arity); \
\               EX Z: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)). \
\                 X <= Occ_fbs_op(Tag, Z) & \
\             (ALL Y: Occ_range(Tag, Arity). Y <= domain(Z)*Tag --> P(Y))\
\       |] ==> P(X) \
\    |] ==> P(X)"
  (fn [major, indstep] =>
    [(rtac (major RS rev_mp) 1),
     (rtac ([major RS CollectD1, major RS CollectD2 RS conjunct1] 
          MRS Occ_fbs_op_fin_bnd_induct) 1),
     (rtac impI 1),
     (rtac indstep 1),
     (REPEAT (atac 1)),
     (REPEAT (eresolve_tac [bexE, conjE] 1)),
     (rtac bexI 1),
     (atac 2),
     (etac conjI 1),
     (rtac (impI RS ballI) 1),
     (etac (spec RS mp RS mp RS mp) 1),
     (REPEAT (eresolve_tac [CollectE, conjE] 2)),
     (REPEAT (atac 1))]);

(** Occ_in_Occ_range **)
qed_goal "Occ_cons_preserves_functionality" OccTools.thy
    "[| ALL z: length(l). functional(nth(l, z)) |] \
\          ==> functional(Occ_cons(T, l))"
  (fn [prem] =>
    [(rtac functionalI 1),
     (etac Occ_consE 1),
     (etac Occ_consE 1),
     (etac Occ_consE 3),
     (dtac (prem RS bspec) 4),
     (ALLGOALS (fast_tac (ZF_cs addSEs list.free_SEs addDs [functionalD])))]);

qed_goal "Occ_cons_preserves_DenseTree" OccTools.thy
    "[| ALL z: length(l). DenseTree(nth(l, z)); l: list(A) |] \
\          ==> DenseTree(Occ_cons(T, l))"
  (fn [prem, l_list] =>
    [(rtac DenseTreeI 1),
     (etac Occ_consE 1),
     (etac (Pair_iff RS iffD1 RS conjE) 1),
     (hyp_subst_tac 1),
     (etac initseg_NilE 1),
     (hyp_subst_tac 1),
     (rtac exI 1),
     (rtac Occ_consI1 1),
     (etac (Pair_iff RS iffD1 RS conjE) 1),
     (hyp_subst_tac 1),
     (etac initseg_ConsE 1),
     (hyp_subst_tac 1),
     (rtac exI 1),
     (rtac Occ_consI1 1),
     (hyp_subst_tac 1),
     (forward_tac [prem RS bspec] 1),
     (etac DenseTreeE 1),
     (REPEAT (ares_tac [Occ_consI2, exI, ltI,
                      l_list RS length_type RS nat_into_Ord] 1))]);

qed_goal "Occ_cons_preserves_CorrectArity" OccTools.thy
    "[| ALL z: length(l). CorrectArity(nth(l, z), U, n); \
\       ALL z: length(l). DenseTree(nth(l, z)); \
\       ALL z: length(l). nth(l, z) ~= 0; \
\       ALL z: length(l). nth(l, z) <= list(nat) * Tag; \
\       T = U ==> n = length(l)\
\    |] ==> CorrectArity(Occ_cons(T, l), U, n)"
  (fn [corr, hier, not_empty, domnth, prem] =>
    [(rtac CorrectArityI 1),
     (etac Occ_consE 1),
     (etac (Pair_iff RS iffD1 RS conjE) 1),
     (forward_tac [sym RS prem] 1),
     (hyp_subst_tac 1),
     (forward_tac [ltD] 1),
     (forward_tac [not_empty RS bspec] 1),
     (forward_tac [domnth RS bspec] 1),
     (forward_tac [hier RS bspec] 1),
     (etac not_emptyE 1),
     (dtac subsetD 1),
     (atac 1),
     (etac SigmaE 1),
     (hyp_subst_tac 1),
     (etac DenseTreeE 1),
     (atac 1),
     (etac initseg_NilI 1),
     (rtac exI 1),
     (asm_simp_tac list_ss 1),
     (etac Occ_consI2 1),
     (atac 1),
     (etac (Pair_iff RS iffD1 RS conjE) 1),
     (forward_tac [corr RS bspec] 1),
     (dtac CorrectArityD1 1),
     (hyp_subst_tac 1),
     (REPEAT (atac 1)),
     (etac exE 1),
     (rtac exI 1),
     (asm_simp_tac list_ss 1),
     (etac Occ_consI2 1),
     (atac 1),
     (etac Occ_consE 1),
     (ALLGOALS ((etac exE) THEN' (etac Occ_consE))),
     (asm_full_simp_tac list_ss 1),
     (fast_tac (ZF_cs addSEs list.free_SEs) 1),
     (asm_full_simp_tac list_ss 2),
     (fast_tac (ZF_cs addSEs list.free_SEs) 2),
     (asm_full_simp_tac (list_ss addsimps [Cons_iff]) 1),
     (REPEAT (etac conjE 1)),
     (forward_tac [sym RS prem] 1),
     (hyp_subst_tac 1),
     (etac leE 1),
     (dtac ltD 1),
     (DEPTH_SOLVE_1 ((etac mem_asym 1) THEN (atac 1))),
     (hyp_subst_tac 1),
     (etac mem_irrefl 1),
     (forward_tac [corr RS bspec] 1),
     (asm_full_simp_tac (list_ss addsimps [Cons_iff]) 1),
     (REPEAT (etac conjE 1)),
     (hyp_subst_tac 1),
     (dtac CorrectArityD2 1),
     (REPEAT (atac 1)),
     (etac notE 1),
     (etac exI 1)]);

qed_goal "Occ_range_domain_lemma" OccTools.thy
    "X: Occ_range(Tag, Arity) ==> X <= list(nat) * Tag"
  (fn [prem] =>
    [(rtac (prem RS Occ_rangeE) 1),
     (cut_facts_tac [Occ_fbs_op_lfp_eq] 1),
     (cut_facts_tac [Occ_fbs_op_bnd_mono] 1),
     (dtac (fin_bnd_set_Pow_lfp_lowerbound RS subsetD) 1),
     (atac 1),
     (dtac PowD 1),
     (etac subst 1),
     (atac 1)]);

qed_goal "Occ_cons_in_fin_bnd_set" OccTools.thy
    "[| bnd_mono(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); \
\      T: Tag; l: list(Pow(list(nat)*Tag)); \
\      ALL z: length(l). nth(l, z): fin_bnd_set(Occ_fbs_dom(Tag), \
\                                                 Occ_fbs_op(Tag)) \
\    |] ==> Occ_cons(T, l): fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  (fn [hmono, t_tag, l_list, prem] =>
    [(rtac (prem RS rev_mp) 1),
     (rtac (l_list RS list_append_induct) 1),
     (ALLGOALS (rtac impI)),
     (ALLGOALS (asm_simp_tac (nth_ss addsimps 
                            [Occ_cons_Nil, Occ_cons_app_last]))),
     (rtac (hmono RS fin_bnd_set_succI) 1),
     (rtac fin_bnd_set_0I 2),
     (SELECT_GOAL (rewrite_goals_tac [Occ_fbs_op_def, list_op_def]) 1),
     (rtac singleton_subsetI 1),
     (rtac SigmaI 1),
     (rtac CollectI 1),
     (rtac (nat_subset_univ RSN (2, list_into_univ)) 1),
     (resolve_tac list.intrs 1),
     (rtac (refl RS disjI1) 1),
     (rtac t_tag 1),
     (rtac (hmono RS fin_bnd_set_UnI) 1),
     (etac mp 1),
     (asm_full_simp_tac (nth_ss addsimps [nth_app_right, length_app,
                                        add_0_right, add_succ_right,
                                        nth_app_left]) 1),
     (rtac (hmono RS fin_bnd_set_succI) 1),
     (SELECT_GOAL (rewrite_goals_tac [Occ_fbs_op_def, list_op_def]) 1),
     (rtac subsetI 1),
     (etac Occ_shiftE 1),
     (hyp_subst_tac 1),
     (rtac SigmaI 1),
     (rtac CollectI 1),
     (rtac (nat_subset_univ RSN (2, list_into_univ)) 1),
     (resolve_tac list.intrs 1),
     (etac length_type 1),
     (dtac (PowD RS subsetD) 1),
     (atac 1),
     (etac SigmaD1 1),
     (rtac disjI2 1),
     (REPEAT (rtac exI 1)),
     (REPEAT (ares_tac [conjI, refl, length_type, domainI] 1)),
     (dtac (PowD RS subsetD) 1),
     (atac 1),
     (etac SigmaD2 1),
     (dres_inst_tac [("x", "length(y)")] bspec 1),
     (asm_simp_tac (nth_ss addsimps [length_app, 
                                        add_0_right, add_succ_right]) 1),
     (asm_full_simp_tac (nth_ss addsimps [nth_app_left]) 1)]);

qed_goal "Occ_ind_cond_Occ_in_Occ_range" OccTools.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); M: Terms |]\
\            ==> Occ(M): Occ_range(Tag, Arity)"
  (fn [major, prem] =>
    [(rtac (prem RS (major RS Occ_ind_cond_Occ_induct)) 1),
     (rtac Occ_rangeI 1),
     (rtac (Occ_consI1 RS not_emptyI) 2),
     (rtac ballI 4),
     (ALLGOALS (resolve_tac [Occ_cons_in_fin_bnd_set,
                           Occ_cons_preserves_functionality,
                           Occ_cons_preserves_DenseTree,
                           Occ_cons_preserves_CorrectArity])),
     (rtac Occ_fbs_op_bnd_mono 1),
     (TRYALL atac),
     (hyp_subst_tac 8),
     (etac sym 8),
     (ALLGOALS ((rtac ballI) THEN' (dtac bspec) THEN' atac)),
     (etac Occ_range_domain_lemma 7),
     (etac Occ_rangeE 4),
     (etac bspec 4),
     (atac 4),
     (ALLGOALS ((etac Occ_rangeE) THEN' atac))]);

qed_goal "Occ_ind_cond_Occ_FinI" OccTools.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); M: Terms |] \
\            ==>  Occ(M): Fin(list(nat) * Tag)"
  (fn [hind, prem] =>
    [(rtac (prem RS (hind RS Occ_ind_cond_Occ_induct)) 1),
     (rtac Occ_cons_FinI 1),
     (etac nth_convert_list_type 1),
     (REPEAT (atac 1))]);

qed_goal "Occ_ind_cond_Occ_not_empty_lemma" OccTools.thy
    "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); M: Terms |]\
\            ==> EX T: Tag. <[], T>: Occ(M)"
  (fn [hind, major] =>
    [(cut_facts_tac [[hind, major] MRS Occ_ind_cond_Occ_in_Occ_range] 1),
     (etac Occ_rangeE 1),
     (rtac Occ_DenseTree_not_empty_lemma 1),
     (REPEAT (ares_tac [[hind, major] MRS Occ_ind_cond_Occ_domain] 1))]);

qed_goal "Occ_range_convert_lemma" OccTools.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); X: Occ_range(Tag, Arity); \
\       !!M. M: Terms ==> P(Occ(M)) |] ==> P(X)"
  (fn [hcons, major, prem] =>
    [(rtac ([hcons, major] MRS Occ_range_existence_lemma RS bexE) 1),
     (etac ssubst 1),
     (etac prem 1)]);

qed_goal "Occ_range_unique_existence_lemma" OccTools.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       X: Occ_range(Tag, Arity) |] ==> EX! M. M: Terms & X = Occ(M)"
  (fn [hcons, hind, major] =>
    [(rtac ([hcons, major] MRS Occ_range_existence_lemma RS bexE) 1),
     (rtac ex1I 1),
     (rtac (hind RS Occ_ind_cond_Occ_inj RS iffD1) 2),
     (TRYALL (etac conjE)),
     (hyp_subst_tac 4),
     (REPEAT (ares_tac [conjI, sym] 1))]);

qed_goal "def_Occinv_type" OccTools.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       X: Occ_range(Tag, Arity) |] ==> Occinv(X): Terms"
  (fn [hcons, hind, hinv, major] =>
    [(rewrite_goals_tac [hinv]),
     (rtac conjunct1 1),
     (rtac ([hcons, hind, major] MRS Occ_range_unique_existence_lemma 
          RS theI) 1)]);

qed_goal "def_Occ_Occinv" OccTools.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       X: Occ_range(Tag, Arity) |] ==> Occ(Occinv(X)) = X"
  (fn [hcons, hind, hinv, major] =>
    [(rewrite_goals_tac [hinv]),
     (rtac (conjunct2 RS sym) 1),
     (rtac ([hcons, hind, major] MRS Occ_range_unique_existence_lemma 
          RS theI) 1)]);

qed_goal "def_Occinv_Occ" OccTools.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       M: Terms |] ==> Occinv(Occ(M)) = M"
  (fn [hcons, hind, hinv, major] =>
    [(rewrite_goals_tac [hinv]),
     (cut_facts_tac [major] 1),
     (rtac the_equality 1),
     (rtac (hind RS Occ_ind_cond_Occ_inj RS iffD1) 2),
     (TRYALL (etac conjE)),
     (REPEAT (ares_tac [refl, conjI, sym] 1))]);

qed_goal "def_Occinv_lemma" OccTools.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       X: Occ_range(Tag, Arity) \
\    |] ==> ALL T: Tag. ALL l: list(Terms). \
\       <[], T>: X & \
\       Arity(T) = length(l) & \
\       (ALL z: length(l). nth(l, z) = Occinv(Occ_subtree(z, X))) \
\     --> Occinv(X) = Term_cons(T, l)"
  (fn [hcons, hind, hinv, major] =>
    [(rtac ([hcons, major] MRS Occ_range_convert_lemma) 1),
     (etac (hind RS Occ_ind_condD) 1),
     (REPEAT (resolve_tac [ballI, impI] 1)),
     (REPEAT (etac conjE 1)),
     (subgoals_tac ["Ta = T", "la = l"] 1),
     (hyp_subst_tac 1),
     (etac ([hcons, hind, hinv] MRS def_Occinv_Occ) 1),
     (forward_tac [hind RS Occ_ind_cond_Occ_in_Occ_range] 2),
     (etac Occ_rangeE 2),
     (etac functionalD 2),
     (atac 2),
     (asm_simp_tac IFOL_ss 2),
     (rtac Occ_consI1 2),
     (rtac nth_inj 1),
     (hyp_subst_tac 2),
     (asm_full_simp_tac IFOL_ss 2),
     (REPEAT (atac 2)),
     (hyp_subst_tac 1),
     (rtac ballI 1),
     (asm_full_simp_tac IFOL_ss 1),
     (forw_inst_tac [("A", "length(la)")] bspec 1),
     (atac 1),
     (etac trans 1),
     (forward_tac [length_type RSN (2, mem_nat_in_nat)] 1),
     (atac 1),
     (res_inst_tac [("P", "%x. Occinv(x) = ?X")] 
      (Occ_subtree_Occ_cons RS ssubst) 1),
     (atac 1),
     (etac map_type 1),
     (etac (hind RS Occ_ind_cond_Occ_domain RS PowI) 1),
     (res_inst_tac [("P", "%x. Occinv(x) = ?X")] 
      (nth_map RS ssubst) 1),
     (atac 1),
     (asm_full_simp_tac nth_ss 1),
     (rtac ([hcons, hind, hinv] MRS def_Occinv_Occ) 1),
     (etac nth_type2 1),
     (asm_full_simp_tac nth_ss 1)]);

qed_goal "def_Occinv" OccTools.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       <[], T>: X; \
\       X: Occ_range(Tag, Arity); \
\       T: Tag; l: list(Terms); Arity(T) = length(l); \
\       ALL z: length(l). nth(l, z) = Occinv(Occ_subtree(z, X)) \
\    |] ==>  Occinv(X) = Term_cons(T, l)"
  (fn hcons::hind::hinv::major::prem::prems =>
    [(rtac ([hcons, hind, hinv, prem] MRS
          def_Occinv_lemma RS bspec RS bspec RS mp) 1),
     (REPEAT (ares_tac ([conjI, major]@prems) 1))]);

qed_goal "def_Occinv2" OccTools.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       Occ_cons(T, l): Occ_range(Tag, Arity); \
\       T: Tag; l: list(Pow(list(nat)*Tag)); Arity(T) = length(l) \
\    |] ==>  Occinv(Occ_cons(T, l)) = Term_cons(T, map(Occinv, l))"
  (fn hcons::hind::hinv::major::prems =>
    [(cut_facts_tac prems 1),
     (rtac ([hcons, hind, hinv, Occ_consI1, major] MRS
          def_Occinv RS trans) 1),
     (rtac refl 5),
     (rtac nth_convert_list_type 2),
     (rtac map_type2 2),
     (TRYALL atac),
     (ALLGOALS (asm_simp_tac (nth_ss addsimps [length_map, nth_map]))),
     (ALLGOALS (rtac ballI)),
     (ALLGOALS (fn i =>
                (subgoals_tac ["x: nat"] i) THEN
                (rtac (length_type RSN (2, mem_nat_in_nat)) (i + 1)) THEN
                (atac (i + 2)) THEN
                (asm_simp_tac IFOL_ss (i + 1)))),
     (asm_simp_tac (IFOL_ss addsimps [Occ_subtree_Occ_cons]) 2),
     (rtac ([hcons, hind, hinv] MRS def_Occinv_type) 1),
     (asm_simp_tac (IFOL_ss addsimps [Occ_subtree_Occ_cons RS sym]) 1),
     (rtac (major RS Occ_rangeE) 1),
     (dtac bspec 1),
     (atac 1),
     (etac (CorrectArityD1 RS exE) 1),
     (rtac Occ_consI1 1),
     (asm_simp_tac IFOL_ss 1),
     (etac (nat_into_Ord RSN (2, ltI)) 1),
     (etac length_type 1),
     (asm_full_simp_tac (IFOL_ss addsimps [app_Nil]) 1),
     (etac Occ_cons_ConsE 1),
     (rtac Occ_subtree_in_Occ_range 1),
     (etac Occ_consI2 1),
     (REPEAT (ares_tac [major] 1))]);

qed_goal "def_Occinv_convert_lemma" OccTools.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       M: Terms; !!X. X: Occ_range(Tag, Arity) ==> P(Occinv(X)) \
\    |] ==> P(M)"
  (fn [hcons, hind, hinv, major, prem] =>
    [(cut_facts_tac [major RS 
                   (hind RS Occ_ind_cond_Occ_in_Occ_range RS prem)] 1),
     (asm_full_simp_tac (IFOL_ss addsimps
                       [[hcons, hind, hinv, major] MRS def_Occinv_Occ]) 1)]);

qed_goal "def_Terms_depth_induct" OccTools.thy
    "[| Occ_cons_cond(Terms, Occ, Tag, Arity); \
\       Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons); \
\       !!x. Occinv(x) == THE M. M: Terms & x = Occ(M); \
\       M: Terms; \
\       !!M Z. [| Occ(M) <= list(nat) * Tag; M: Terms; \
\             Z: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); \
\             Occ(M) <= Occ_fbs_op(Tag, Z); \
\             ALL N: Terms. Occ(N) <= domain(Z)*Tag --> P(N)\
\       |] ==> P(M) \
\    |] ==> P(M)"
  (fn [hcons, hind, hinv, major, indstep] =>
    [(rtac ([hcons, hind, hinv, major] MRS def_Occinv_convert_lemma) 1),
     (etac Occ_range_depth_induct 1),
     (safe_tac ZF_cs),
     (rtac indstep 1),
     (etac ([hcons, hind, hinv] MRS def_Occinv_type) 2),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps
                            [[hcons, hind, hinv] MRS def_Occ_Occinv]))),
     (REPEAT (ares_tac [bexI, conjI, ballI, impI] 1)),
     (dtac (bspec RS mp) 1),
     (etac (hind RS Occ_ind_cond_Occ_in_Occ_range) 1),
     (asm_full_simp_tac (IFOL_ss addsimps
                       [[hcons, hind, hinv] MRS def_Occinv_Occ]) 2),
     (atac 1)]);


