(*
    File:        FinCard.thy
    Time-stamp:  <2020-06-22T03:36:42Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory FinCard imports ZF.Finite ZF.Cardinal begin

lemma Fin_subset2:
  assumes "X: Fin(A)"
      and "X <= B"
    shows "X: Fin(B)"
apply (rule assms(2) [THEN rev_mp])
apply (rule assms(1) [THEN Fin_induct])
apply (rule impI)
apply (rule Fin.emptyI)
apply (rule impI)
apply (erule cons_subsetE)
apply (rule Fin.consI)
apply (drule_tac [2] mp)
apply assumption+
done

lemma Fin_domainI [TC]:
    "X: Fin(A*B) ==> domain(X): Fin(A)"
apply (erule Fin_induct)
apply (erule_tac [2] SigmaE)
apply simp_all
done

lemma Fin_rangeI [TC]:
    "X: Fin(A*B) ==> range(X): Fin(B)"
apply (erule Fin_induct)
apply (erule_tac [2] SigmaE)
apply simp_all
done

lemma Fin_RepFunI [TC]:
    "[| X: Fin(A); !!x. x: A ==> f(x): B |] ==> {f(x). x: X}: Fin(B)"
apply (erule Fin_induct)
apply simp_all
done

lemmas Fin_imp_Finite = Fin_into_Finite
lemmas Finite_imp_Fin = Finite_into_Fin

lemma Finite_imp_card_nat [TC]:
    "Finite(A) ==> |A|: nat"
apply (unfold Finite_def)
apply (erule bexE)
apply (drule cardinal_cong)
apply (erule ssubst)
apply (rule lt_nat_in_nat)
apply (rule Ord_cardinal_le)
apply (erule nat_into_Ord)
apply (erule nat_succI)
done

lemma Fin_complete_induct_lemma:
 "n: nat ==> (ALL X: Fin(A). |X| = n --> 
   (ALL x: Fin(A). (ALL y. y: Fin(A) & |y| < |x| --> P(y)) --> P(x)) 
   --> P(X))"
apply (erule complete_induct)
apply clarsimp
apply (erule bspec [THEN mp])
apply assumption
apply clarsimp
apply (drule ltD)
apply simp
done

lemma Fin_complete_induct:
  assumes major: "X: Fin(A)"
  and indstep: "!!x. [| x: Fin(A); 
                       ALL y. y: Fin(A) & |y| < |x| --> P(y)
                     |] ==> P(x)"
  shows "P(X)"
apply (rule major [THEN Fin_into_Finite, THEN Finite_imp_card_nat,
                   THEN Fin_complete_induct_lemma,
                   THEN bspec, THEN mp, THEN mp])
apply ((rule major refl ballI impI indstep) | assumption)+
done

lemma Finite_lepoll_imp_le:
  assumes major: "A \<lesssim> B"
  and prem: "Finite(B)"
  shows "|A| \<le> |B|"
apply (insert lepoll_Finite [OF major prem] prem major)
apply (unfold Finite_def cardinal_def)
apply clarify
apply (rule le_trans)
apply (rule Least_le)
apply (erule eqpoll_sym)
apply (erule nat_into_Ord)
apply (rule_tac P="%x. n \<le> x" in ssubst)
apply (rule Least_equality)
apply (erule eqpoll_sym)
apply (erule nat_into_Ord)
apply (rule notI)
apply (drule eqpoll_trans, assumption)
apply (frule lt_nat_in_nat)
apply assumption
apply (drule nat_eqpoll_iff [THEN iffD1], assumption, assumption)
apply hypsubst
apply (erule lt_irrefl)
apply (rule nat_lepoll_imp_le)
apply assumption+
apply (rule lepoll_trans)
apply (rule eqpoll_sym [THEN eqpoll_imp_lepoll], assumption)
apply (rule lepoll_trans, assumption)
apply (erule eqpoll_imp_lepoll)
done

lemma Finite_cardinal_succ:
    "Finite(A) ==> |succ(A)| = succ(|A|)"
apply (unfold Finite_def)
apply (erule bexE)
apply (rule_tac b="|succ(n)|" in trans)
apply (rule cardinal_cong) 
apply (simp only: succ_def)
apply (blast elim!: mem_irrefl intro: cons_eqpoll_cong)
apply (drule cardinal_cong)
apply (simp add: nat_into_Card [THEN Card_cardinal_eq])
done

lemma Finite_cardinal_cons:
  assumes major: "Finite(A)"
  shows "a ~: A ==> |cons(a, A)| = succ(|A|)"
apply (rule major [THEN Finite_cardinal_succ, THEN [2] trans])
apply (rule cardinal_cong)
apply (unfold succ_def)
apply (blast elim!: mem_irrefl intro: eqpoll_refl cons_eqpoll_cong)
done

lemmas FinCard_simps = Finite_cardinal_cons cons_absorb cardinal_0

end
