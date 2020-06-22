(*
    File:        Poset.thy
    Time-stamp:  <2020-06-22T03:40:26Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory Poset imports ZF FinCard begin

definition poset :: "[[i,i]=>o, i]=>o" where
"poset(R, P) == (ALL x: P. R(x, x)) &
  (ALL x: P. ALL y: P. R(x, y) & R(y, x) --> x = y) &
  (ALL x: P. ALL y: P. ALL z: P. R(x, y) & R(y, z) --> R(x, z))"

definition chain :: "[[i,i]=>o, i]=>o" where
"chain(R, P) == poset(R, P)
   & (ALL x: P. ALL y: P. R(x, y) | R(y, x))"

definition invrel :: "[[i, i]=>o, i, i]=>o" where
"invrel(R, x, y) == R(y, x)"

definition least :: "[[i,i]=>o, i, i]=>o" where
"least(R, P, x) == x: P & (ALL y: P. R(x, y))"

definition greatest :: "[[i,i]=>o, i, i]=>o" where
"greatest(R, P, x) == x: P & (ALL y: P. R(y, x))"

definition minimal :: "[[i, i]=>o, i, i]=>o" where
"minimal(R, P, x) == x: P & (ALL y: P. R(y, x) --> y = x)"

definition maximal :: "[[i, i]=>o, i, i]=>o" where
"maximal(R, P, x) == x: P & (ALL y: P. R(x, y) --> y = x)"

definition downset :: "[[i, i]=>o, i, i]=>i" where
"downset(R, P, x) == {y: P. R(y, x)}"

definition upset :: "[[i, i]=>o, i, i]=>i" where
"upset(R, P, x) == {y: P. R(x, y)}"

definition upperbound :: "[[i, i]=>o, i, i]=>i" where
"upperbound(R, P, S) == {x: P. ALL y: S. R(y, x)}"

definition lowerbound :: "[[i, i]=>o, i, i]=>i" where
"lowerbound(R, P, S) == {x: P. ALL y: S. R(x, y)}"

(** poset **)
lemma posetI:
  "[| !!x. x: P ==> R(x, x); 
      !!x y. [| x: P; y: P; R(x, y); R(y, x) |] ==> x = y; 
      !!x y z. [| x: P; y: P; z: P; R(x, y); R(y, z) |] ==> R(x, z)
   |] ==> poset(R, P)"
apply (unfold poset_def)
apply blast
done

lemma poset_reflD:
  "[| poset(R, P); x: P |] ==> R(x, x)"
apply (unfold poset_def)
apply blast
done

lemma poset_antisymD:
  "[| poset(R, P); R(x, y); R(y, x); x: P; y: P |] ==> x = y"
apply (unfold poset_def)
apply blast
done

lemma poset_transD:
  "[| poset(R, P); R(x, y); R(y, z); x: P; y: P; z: P |] ==> R(x, z)"
apply (unfold poset_def)
apply blast
done

lemma poset_subset:
  "[| S <= P; poset(R, P) |] ==> poset(R, S)"
apply (rule posetI)
apply (drule subsetD, assumption)
apply (erule poset_reflD, assumption)
apply (erule poset_antisymD, assumption+)
apply (erule subsetD, assumption)+
apply (erule poset_transD, assumption+)
apply (erule subsetD, assumption)+
done

lemma poset_invrel_iff:
  "poset(invrel(R), P) <-> poset(R, P)"
apply (unfold poset_def invrel_def)
apply blast
done

(** chain **)
lemma chainI:
  "[| poset(R, P); !!x y. [| x: P; y: P |] ==> R(x, y) | R(y, x) |]
      ==> chain(R, P)"
apply (unfold chain_def)
apply blast
done

lemma chain_imp_poset:
    "chain(R, P) ==> poset(R, P)"
apply (unfold chain_def)
apply blast
done

lemmas chainD1 = chain_imp_poset

lemma chainD2:
  "[| chain(R, P); x: P; y: P |] ==> R(x, y) | R(y, x)"
apply (unfold chain_def)
apply blast
done

lemma chain_subset:
    "[| S <= P; chain(R, P) |] ==> chain(R, S)"
apply (blast intro: chainI poset_subset dest: chainD1 chainD2)
done

lemma chain_invrel_iff:
  "chain(invrel(R), P) <-> chain(R, P)"
apply (unfold chain_def)
apply (simp add: poset_invrel_iff)
apply (unfold invrel_def)
apply blast
done

(** least/greatest **)
lemma leastI:
  "[| !!y. y: P ==> R(x, y); x: P |] ==> least(R, P, x)"
apply (unfold least_def)
apply blast
done

lemma leastD1:
  "least(R, P, x) ==> x: P"
apply (unfold least_def)
apply blast
done

lemma leastD2:
  "[| least(R, P, x); y: P |] ==> R(x, y)"
apply (unfold least_def)
apply blast
done

lemma least_unique:
  "[| least(R, P, x); least(R, P, y); poset(R, P) |] ==> x = y"
apply (erule poset_antisymD)
apply (erule leastD2, erule leastD1) 
apply (erule leastD2, erule leastD1)
apply (erule leastD1)
apply (erule leastD1)
done

lemma least_subset:
  "[| S <= P; least(R, P, x); x: S |] ==> least(R, S, x)"
apply (rule leastI)
apply (drule subsetD)
apply (drule_tac [2] leastD2)
by assumption+

lemma Finite_non_empty_chain_has_least_element:
  assumes major: "Finite(P)"
  and prem1: "chain(R, P)"
  and prem2: "P ~= 0"
  shows "EX x. least(R, P, x)"
apply (rule prem2 [THEN rev_mp])
apply (rule prem1 [THEN rev_mp])
apply (rule major [THEN Finite_into_Fin, THEN Fin_induct])
apply blast
apply (intro impI)
apply (case_tac "y = 0")
apply hypsubst
apply (rule exI)
apply (rule leastI)
apply (rule_tac [2] singletonI)
apply (erule singletonE)
apply hypsubst
apply (erule chain_imp_poset [THEN poset_reflD])
apply (rule singletonI)
apply (drule mp [THEN mp])
apply (rule chain_subset)
apply (rule subset_consI)
apply assumption+
apply (erule exE)
apply (frule chainD2)
apply (rule consI1)
apply (rule consI2)
apply (erule leastD1)
apply (erule disjE)
apply (rename_tac [2] v)
apply (rule_tac x="x" in exI)
apply (rule_tac [2] x="v" in exI)
apply (rule_tac [2] leastI)
apply (rule leastI)
apply (rule_tac [4] consI2)
apply safe
apply (erule chain_imp_poset [THEN poset_reflD])
apply (erule_tac [2] chain_imp_poset [THEN poset_transD])
prefer 2 apply assumption
apply (rule_tac [4] consI2)
apply (erule_tac [5] consI2)
apply (erule_tac [2] leastD2)
apply (erule_tac [5] leastD2)
apply (assumption | (rule consI1 leastD1))+
done

lemma least_invrel_iff:
    "least(invrel(R), P, x) <-> greatest(R, P, x)"
apply (unfold least_def greatest_def invrel_def)
apply (rule iff_refl)
done

lemma greatest_invrel_iff:
    "greatest(invrel(R), P, x) <-> least(R, P, x)"
apply (unfold least_def greatest_def invrel_def)
apply (rule iff_refl)
done

(** minimal/maximal **)
lemma minimalI:
  "[| !!y. [| y: P;  R(y, x) |] ==> y = x; x: P |] ==> minimal(R, P, x)"
apply (unfold minimal_def)
apply blast
done

lemma minimalD1:
  "minimal(R, P, x) ==> x: P"
apply (unfold minimal_def)
apply blast
done

lemma minimalD2:
  "[| minimal(R, P, x); R(y, x); y: P |] ==> y = x"
apply (unfold minimal_def)
apply blast
done

lemma minimal_subset:
  "[| S <= P; minimal(R, P, x); x: S |] ==> minimal(R, S, x)"
apply (rule minimalI)
apply (erule minimalD2)
apply assumption
apply (erule subsetD)
apply assumption+
done

lemma least_imp_minimal:
  "[| least(R, P, x); poset(R, P) |] ==> minimal(R, P, x)"
apply (rule minimalI)
apply (erule poset_antisymD)
apply (erule_tac [2] leastD2)
apply (assumption | (erule leastD1))+
done

lemma chain_minimal_imp_least:
  "[| minimal(R, P, x); chain(R, P) |] ==> least(R, P, x)"
apply (rule leastI)
apply (rule chainD2 [THEN disjE])
apply assumption
apply (erule minimalD1)
apply assumption+
apply (drule minimalD2)
apply assumption+
apply hypsubst
apply (erule chainD1 [THEN poset_reflD], assumption)
apply (erule minimalD1)
done

lemma minimal_invrel_iff:
    "minimal(invrel(R), P, x) <-> maximal(R, P, x)"
apply (unfold minimal_def maximal_def invrel_def)
apply (rule iff_refl)
done

lemma maximal_invrel_iff:
    "maximal(invrel(R), P, x) <-> minimal(R, P, x)"
apply (unfold minimal_def maximal_def invrel_def)
apply (rule iff_refl)
done

(** upset/downset **)
lemma upsetI:
  "[| y: P; R(x, y) |] ==> y: upset(R, P, x)"
apply (unfold upset_def)
apply blast
done

lemma upsetE:
  "[| y: upset(R, P, x); [| y: P; R(x, y) |] ==> Q |] ==> Q"
apply (unfold upset_def)
apply blast
done

lemma upset_subset:
    "upset(R, P, x) <= P"
apply (blast elim!: upsetE)
done

lemma least_upset:
  "[| poset(R, P); x: P |] ==> least(R, upset(R, P, x), x)"
apply (rule leastI)
apply (erule upsetE)
apply (assumption | (rule upsetI) | (erule poset_reflD))+
done

lemma upset_invrel_eq:
    "upset(invrel(R), P, x) = downset(R, P, x)"
apply (unfold downset_def upset_def invrel_def)
apply (rule refl)
done

lemma downset_invrel_eq:
    "downset(invrel(R), P, x) = upset(R, P, x)"
apply (unfold downset_def upset_def invrel_def)
apply (rule refl)
done

(** upperbound/lowerbound **)
lemma upperboundI:
  "[| x: P; !!y. y: S ==> R(y, x) |] ==> x: upperbound(R, P, S)"
apply (unfold upperbound_def)
apply blast
done

lemma upperboundE:
  "[| x: upperbound(R, P, S); [| x: P; ALL y: S. R(y, x) |] ==> Q |] ==> Q"
apply (unfold upperbound_def)
apply blast
done

lemma upperbound_invrel_eq:
    "upperbound(invrel(R), P, S) = lowerbound(R, P, S)"
apply (unfold lowerbound_def upperbound_def invrel_def)
apply (rule refl)
done

lemma lowerbound_invrel_eq:
    "lowerbound(invrel(R), P, S) = upperbound(R, P, S)"
apply (unfold lowerbound_def upperbound_def invrel_def)
apply (rule refl)
done

(** Prove symmetric theorems **)
lemma greatestI:
  "[| !!y. y: P ==> R(y, x); x: P |] ==> greatest(R, P, x)"
apply (unfold greatest_def)
apply blast
done

lemma greatestD1:
  "greatest(R, P, x) ==> x: P"
apply (unfold greatest_def)
apply blast
done

lemma greatestD2:
  "[| greatest(R, P, x); y: P |] ==> R(y, x)"
apply (unfold greatest_def)
apply blast
done

lemma greatest_unique:
  "[| greatest(R, P, x); greatest(R, P, y); poset(R, P) |] ==> x = y"
apply (simp only: least_invrel_iff [THEN iff_sym])
apply (subst (asm) poset_invrel_iff [THEN iff_sym])
apply (erule least_unique)
apply assumption+
done

lemma greatest_subset:
  "[| S <= P; greatest(R, P, x); x: S |] ==> greatest(R, S, x)"
apply (rule greatestI)
apply (drule subsetD)
apply (drule_tac [2] greatestD2)
by assumption+

lemma Finite_non_empty_chain_has_greatest_element:
  assumes major: "Finite(P)"
  and prem1: "chain(R, P)"
  and prem2: "P ~= 0"
  shows "EX x. greatest(R, P, x)"
apply (insert major prem1 prem2)
apply (simp only: least_invrel_iff [THEN iff_sym])
apply (subst (asm) chain_invrel_iff [THEN iff_sym])
apply (rule Finite_non_empty_chain_has_least_element)
apply assumption+
done

lemma maximalI:
  "[| !!y. [| y: P;  R(x, y) |] ==> y = x; x: P |] ==> maximal(R, P, x)"
apply (unfold maximal_def)
apply blast
done

lemma maximalD1:
  "maximal(R, P, x) ==> x: P"
apply (unfold maximal_def)
apply blast
done

lemma maximalD2:
  "[| maximal(R, P, x); R(x, y); y: P |] ==> y = x"
apply (unfold maximal_def)
apply blast
done

lemma maximal_subset:
  "[| S <= P; maximal(R, P, x); x: S |] ==> maximal(R, S, x)"
apply (rule maximalI)
apply (erule maximalD2)
apply assumption
apply (erule subsetD)
apply assumption+
done

lemma greatest_imp_maximal:
  "[| greatest(R, P, x); poset(R, P) |] ==> maximal(R, P, x)"
apply (rule maximalI)
apply (erule poset_antisymD)
apply (erule_tac [1] greatestD2)
apply (assumption | (erule greatestD1))+
done

lemma chain_maximal_imp_greatest:
  "[| maximal(R, P, x); chain(R, P) |] ==> greatest(R, P, x)"
apply (simp only: least_invrel_iff [THEN iff_sym])
apply (simp only: minimal_invrel_iff [THEN iff_sym])
apply (subst (asm) chain_invrel_iff [THEN iff_sym])
apply (rule chain_minimal_imp_least)
apply assumption+
done

lemma downsetI:
  "[| y: P; R(y, x) |] ==> y: downset(R, P, x)"
apply (unfold downset_def)
apply blast
done

lemma downsetE:
  "[| y: downset(R, P, x); [| y: P; R(y, x) |] ==> Q |] ==> Q"
apply (unfold downset_def)
apply blast
done

lemma downset_subset:
    "downset(R, P, x) <= P"
apply (blast elim!: downsetE)
done

lemma greatest_downset:
  "[| poset(R, P); x: P |] ==> greatest(R, downset(R, P, x), x)"
apply (rule greatestI)
apply (erule downsetE)
apply (assumption | (rule downsetI) | (erule poset_reflD))+
done

lemma lowerboundI:
  "[| x: P; !!y. y: S ==> R(x, y) |] ==> x: lowerbound(R, P, S)"
apply (unfold lowerbound_def)
apply blast
done

lemma lowerboundE:
  "[| x: lowerbound(R, P, S); [| x: P; ALL y: S. R(x, y) |] ==> Q |] ==> Q"
apply (unfold lowerbound_def)
apply blast
done

end
