(*
    File:        FinCard.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open FinCard;

(** Finite **)
qed_goal "Fin_subset2" Finite.thy
    "[| X: Fin(A); X <= B |] ==>  X: Fin(B)"
  (fn [prem1, prem2] =>
    [(rtac (prem2 RS rev_mp) 1),
     (rtac (prem1 RS Fin_induct) 1),
     (rtac impI 1),
     (rtac Fin.emptyI 1),
     (rtac impI 1),
     (etac cons_subsetE 1),
     (rtac Fin.consI 1),
     (etac mp 2),
     (REPEAT (atac 1))]);

qed_goal "Fin_domainI" Finite.thy
    "X: Fin(A*B) ==> domain(X): Fin(A)"
  (fn [prem] =>
    [(rtac (prem RS Fin_induct) 1),
     (etac SigmaE 2),
     (hyp_subst_tac 2),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps [domain_cons, domain_0]))),
     (REPEAT (ares_tac Fin.intrs 1))]);

qed_goal "Fin_RepFunI" Finite.thy
    "[| X: Fin(A); !!x. x: A ==> f(x): B |] ==> {f(x). x: X}: Fin(B)"
  (fn [major, prem] =>
    [(rtac (major RS Fin_induct) 1),
     (ALLGOALS (simp_tac ZF_ss)),
     (REPEAT (ares_tac (Fin.intrs @ [prem]) 1))]);

(** Cardinal **)
qed_goalw "Finite_imp_Fin" FinCard.thy [Finite_def]
    "Finite(A) ==> A: Fin(A)"
  (fn [prem] =>
    [(rtac (prem RS bexE) 1),
     (eres_inst_tac [("P", "A eqpoll x")] rev_mp 1),
     (res_inst_tac [("x", "A")] spec 1),
     (etac nat_induct 1),
     (safe_tac (ZF_cs addSDs [eqpoll_0_is_0])),
     (excluded_middle_tac "xb = 0" 2),
     (etac not_emptyE 2),
     (forw_inst_tac [("A", "xb")] Diff_sing_eqpoll 2),
     (atac 2),
     (dtac (spec RS mp) 2),
     (atac 2),
     (dtac Fin_subset2 2),
     (rtac Diff_subset 2),
     (res_inst_tac [("P", "%x. x: ?X")] subst 2),
     (rtac cons_Diff 2),
     (atac 2),
     (hyp_subst_tac 3),
     (REPEAT (ares_tac Fin.intrs 1))]);

qed_goal "Fin_imp_Finite" FinCard.thy
    "A: Fin(B) ==> Finite(A)"
  (fn [prem] =>
    [(rtac (prem RS Fin_induct) 1),
     (rtac lepoll_nat_imp_Finite 1),
     (rtac lepoll_refl 1),
     (rtac nat_0I 1),
     (etac Finite_cons 1)]);

qed_goalw "Finite_imp_card_nat" FinCard.thy [Finite_def]
    "Finite(A) ==> |A|: nat"
  (fn [prem] =>
    [(rtac (prem RS bexE) 1),
     (dtac cardinal_cong 1),
     (etac ssubst 1),
     (rtac lt_nat_in_nat 1),
     (rtac Ord_cardinal_le 1),
     (etac nat_into_Ord 1),
     (etac nat_succI 1)]);

qed_goal "Fin_complete_induct" FinCard.thy
    "[| X: Fin(A); \
\       !!x. [| x: Fin(A); ALL y. y: Fin(A) & |y| < |x| --> P(y) |] \
\          ==> P(x) \
\    |] ==> P(X)"
  (fn [major, indstep] =>
   let
       val Fin_complete_induct_lemma = prove_goal FinCard.thy
       "n: nat ==> (ALL X: Fin(A). |X| = n --> \
\          (ALL x: Fin(A). (ALL y. y: Fin(A) & |y| < |x| --> P(y)) --> P(x)) \
\        --> P(X))"
	   (fn [major] =>
	    [(rtac (major RS complete_induct) 1),
	     (safe_tac ZF_cs),
	     (rtac (bspec RS mp) 1),
	     (REPEAT (atac 1)),
	     (safe_tac ZF_cs),
	     (etac (bspec RS bspec RS mp RS mp) 1),
	     (etac ltD 1),
	     (safe_tac ZF_cs)])
   in
    [(rtac (major RS Fin_imp_Finite RS Finite_imp_card_nat
	  RS Fin_complete_induct_lemma RS bspec RS mp RS mp) 1),
     (REPEAT (ares_tac [major, refl, ballI, impI, indstep] 1))]
   end);

qed_goal "cardinal_0" FinCard.thy
    "|0| = 0"
  (fn _ =>
    [(rtac (Card_0 RS Card_cardinal_eq) 1)]);

qed_goalw "Finite_leqpoll_imp_le" FinCard.thy [cardinal_def]
    "[| A lepoll B; Finite(B) |] ==> |A| le |B|"
  (fn [major, prem] =>
    [(cut_facts_tac [[major, prem] MRS lepoll_Finite, prem] 1),
     (rewrite_goals_tac [Finite_def]),
     (safe_tac ZF_cs),
     (rtac le_trans 1),
     (rtac Least_le 1),
     (etac eqpoll_sym 1),
     (etac nat_into_Ord 1),
     (res_inst_tac [("P", "%x. ?X le x")] ssubst 1),
     (rtac Least_equality 1),
     (etac eqpoll_sym 1),
     (etac nat_into_Ord 1),
     (rtac notI 1),
     ((dtac eqpoll_trans 1) THEN (atac 1)),
     (forward_tac [lt_nat_in_nat] 1),
     ((dtac (nat_eqpoll_iff RS iffD1) 2) THEN (atac 2) THEN (atac 2)),
     (hyp_subst_tac 2),
     (etac lt_irrefl 2),
     (rtac nat_lepoll_imp_le 2),
     (rtac lepoll_trans 4),
     (rtac lepoll_trans 4),
     (rtac major 5),
     (etac (eqpoll_sym RS eqpoll_imp_lepoll) 4),
     (etac eqpoll_imp_lepoll 4),
     (REPEAT (atac 1))]);

qed_goalw "Finite_cardinal_succ" FinCard.thy [Finite_def]
    "Finite(A) ==> |succ(A)| = succ(|A|)"
  (fn [prem] =>
    [(rtac (prem RS bexE) 1),
     (res_inst_tac [("b", "|succ(x)|")] trans 1),
     (dtac cardinal_cong 2),
     (asm_simp_tac (arith_ss addsimps 
	      [nat_into_Card RS Card_cardinal_eq]) 2),
     (rtac cardinal_cong 1),
     (rewrite_goals_tac [succ_def]),
     (fast_tac (ZF_cs addSEs [mem_irrefl] addIs [cons_eqpoll_cong]) 1)]);

qed_goal "Finite_cardinal_cons" FinCard.thy
    "[| Finite(A); a ~: A |] ==> |cons(a, A)| = succ(|A|)"
  (fn [major, prem] =>
    [(rtac (major RS Finite_cardinal_succ RSN (2, trans)) 1),
     (rtac cardinal_cong 1),
     (cut_facts_tac [prem] 1),
     (rewrite_goals_tac [succ_def]),
     (fast_tac (ZF_cs addSEs [mem_irrefl] addIs [eqpoll_refl,
					       cons_eqpoll_cong]) 1)]);

val FinCard_simps = [Finite_cardinal_cons, cons_absorb, cardinal_0];

