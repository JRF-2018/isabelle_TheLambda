(*
    File:        FinBndEx.thy
    Time-stamp:  <2015-12-20T11:46:36Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory FinBndEx imports FinBnd begin

definition h_nat :: "i=>i" where
"h_nat(X) == {0} Un {succ(x). x: X}"

definition h_tn :: "i=>i" where
"h_tn(X) == if(nat: X | X = nat, succ(nat), h_nat(X))"

lemma subset_consE:
  assumes major: "x <= cons(a, B)"
  and prem1: "a: x ==> R"
  and prem2: "x <= B ==> R"
  shows "R"
apply (rule excluded_middle [THEN disjE])
apply (erule_tac [2] prem1)
apply (rule prem2)
apply (rule subsetI)
apply (frule major [THEN subsetD])
apply (erule consE)
apply hypsubst
apply (erule notE)
apply assumption+
done

lemma subset_succE:
  "[| x <= succ(n); n: x ==> R; x <= n ==> R |] ==> R"
apply (unfold succ_def)
apply (erule subset_consE)
apply blast+
done

lemma succ_self_neq:
  "succ(n) = n ==> P"
apply (unfold succ_def)
apply (rule mem_irrefl)
apply (erule equalityD1 [THEN subsetD])
apply (rule consI1)
done

lemma h_nat_bnd_mono:
  "bnd_mono(Inf, h_nat)"
apply (unfold bnd_mono_def h_nat_def)
apply (rule nat_bnd_mono [unfolded bnd_mono_def])
done

lemma h_nat_lfp:
    "nat = lfp(Inf, h_nat)"
apply (unfold lfp_def h_nat_def nat_def)
apply (rule refl)
done

lemma h_tn_bnd_mono:
    "bnd_mono(succ(nat), h_tn)"
apply (rule bnd_monoI)
apply (unfold h_tn_def)
apply (rule if_P [THEN ssubst])
apply (rule succI1 [THEN disjI1])
apply (rule subset_refl)
apply (rule_tac P1="%x. (if nat: W | W = nat then succ(nat) else h_nat(W)) <= x"
    in split_if [THEN iffD2])
apply (rule conjI)
apply (rule impI)
apply (rule_tac P1="%x. x <= succ(nat)"
    in split_if [THEN iffD2])
apply (rule conjI)
apply (rule subset_refl [THEN impI])
apply (rule impI)
apply (erule subset_succE)
apply (erule notE)
apply (erule disjI1)
apply (rule subset_succI [THEN [2] subset_trans])
apply (rule h_nat_lfp [THEN ssubst])
apply (rule h_nat_bnd_mono [THEN lfp_lemma2, THEN [2] subset_trans])
apply (rule h_nat_bnd_mono [THEN bnd_monoD2])
apply (erule h_nat_lfp [THEN subst])
apply (rule lfp_subset)
apply (rule impI)
apply (rule_tac P1="%x. x<= h_nat(X)" in split_if [THEN iffD2])
apply (rule conjI)
apply (rule impI)
apply (erule notE)
apply (erule disjE)
apply (rule disjI1)
apply (erule subsetD)
apply assumption
apply hypsubst
apply (erule_tac x="X" in subset_succE)
apply (erule disjI1)
apply (rule disjI2)
apply (erule equalityI, assumption)
apply (rule impI)
apply (erule h_nat_bnd_mono [THEN bnd_monoD2])
apply (erule_tac x="X" in subset_succE)
apply (erule notE)
apply (erule disjI1)
apply (erule subset_trans)
apply (rule h_nat_lfp [THEN ssubst])
apply (rule lfp_subset)
done

lemma h_tn_lfp:
    "lfp(succ(nat), h_tn) = succ(nat)"
apply (rule h_tn_bnd_mono [THEN lfpI])
apply (unfold h_tn_def)
apply (drule_tac P1="%x. x<= X" in split_if [THEN iffD1])
apply (erule conjE)
apply (case_tac "nat:X | X = nat")
apply (drule mp, assumption, assumption)
apply (drule mp)
apply (erule subset_succE)
apply (erule notE)
apply (erule disjI1)
apply (rule notE, assumption)
apply (drule mp, assumption)
apply (rule disjI2)
apply (rule equalityI)
apply assumption
apply (rule h_nat_lfp [THEN ssubst])
apply (erule lfp_lowerbound)
apply (erule subset_trans)
apply (rule h_nat_lfp [THEN ssubst])
apply (rule lfp_subset)
apply assumption
apply (rule if_P [THEN ssubst])
apply (rule succI1 [THEN disjI1])
apply (rule subset_refl)
done

lemma FinBndEx_lemma1:
  "n: A ==> ~(A: n | n = A)"
apply (rule notI)
apply (erule disjE)
apply (erule mem_asym, assumption)
apply hypsubst
apply (erule mem_irrefl)
done

lemma FinBndEx_lemma2:
    "n: nat ==> nat_rec(n, 0, %n r. h_nat(r)) = n"
apply (unfold h_nat_def)
apply (erule nat_induct)
apply (simp_all add: nat_rec_0 nat_rec_succ)
apply (rule equalityI)
apply (rule subsetI)
apply (erule UnE)
apply (erule singletonE)
apply hypsubst
apply (rule ltD)
apply (erule nat_into_Ord [THEN Ord_0_le])
apply (erule RepFunE)
apply hypsubst
apply (rule ltD)
apply (erule ltI [THEN succ_leI])
apply (erule nat_into_Ord)
apply (rule subsetI)
apply (rename_tac v)
apply (frule_tac i="v" in ltI)
apply (erule nat_into_Ord [THEN Ord_succ])
apply (frule lt_nat_in_nat)
apply (erule nat_succI)
apply (erule_tac n="v" in natE)
apply hypsubst
apply blast
apply (rule UnI2)
apply hypsubst
apply (rule RepFunI)
apply (rule ltD)
apply (rule succ_leE)
apply (erule ltI)
apply (erule nat_into_Ord [THEN Ord_succ])
done

lemma FinBndEx_lemma3:
  "n: nat ==> nat_rec(n, 0, %x r. h_tn(r)) = nat_rec(n, 0, %x r. h_nat(r))"
apply (unfold h_tn_def)
apply (erule nat_induct)
apply (simp_all add: nat_rec_0 nat_rec_succ)
apply (simp only: FinBndEx_lemma2)
apply (rule impI)
apply (drule FinBndEx_lemma1)
apply (erule notE, assumption)
done

lemma Singleton_of_the_nat_is_an_finite_subset_of_succ_nat:
  "{nat}: Fin(lfp(succ(nat), h_tn))"
apply (rule_tac P="%x. {nat}: Fin(x)" in h_tn_lfp [THEN ssubst])
apply (rule Fin.intros)
apply (rule succI1)
apply (rule Fin.intros)
done

lemma Singleton_of_the_nat_is_not_in_the_finitely_bound_set:
  "{nat} ~: fin_bnd_set(succ(nat), h_tn)"
apply (rule notI)
apply (erule fin_bnd_setE)
apply (unfold fin_bnd_def)
apply (erule bexE)
apply (erule_tac P="{nat} <= nat_rec(n, 0, %n r. h_tn(r))"
        in rev_mp)
apply (simp add: FinBndEx_lemma2 FinBndEx_lemma3)
apply (rule notI)
apply (erule mem_asym, assumption)
done

lemma h_nat_bnd_cont:
    "bnd_cont(Inf, h_nat)"
apply (rule bnd_contI)
apply (rule_tac [2] h_nat_bnd_mono [THEN bnd_monoD1])
apply (unfold h_nat_def)
apply (rule equalityI)
prefer 2 apply blast
apply (rule subsetI)
apply (erule UnE)
apply (erule singletonE)
apply hypsubst
apply (erule not_emptyE)
apply (erule UN_I)
apply (rule singletonI [THEN UnI1])
apply (erule RepFunE)
apply (erule UnionE)
apply (erule UN_I)
apply (rule UnI2)
apply hypsubst
apply (rule RepFunI, assumption)
done

lemma nat_not_in_the_fin_bnd_set:
    "nat ~: fin_bnd_set(Inf, h_nat)"
apply (unfold fin_bnd_set_def fin_bnd_def)
apply (rule notI)
apply (erule CollectE)
apply (erule bexE)
apply (simp only: FinBndEx_lemma2)
apply (rule mem_imp_not_eq [THEN notE])
apply (rule_tac [2] equalityI)
prefer 3 apply assumption
apply assumption
apply (erule ltI [THEN leI, THEN le_imp_subset])
apply (rule Ord_nat)
done

lemma Pow_lfp_of_h_nat_is_not_equal_to_the_fin_bnd_set:
    "Pow(lfp(Inf, h_nat)) ~= fin_bnd_set(Inf, h_nat)"
apply (rule notI)
apply (rule nat_not_in_the_fin_bnd_set [THEN notE])
apply (erule subst)
apply (rule PowI)
apply (rule h_nat_lfp [THEN subst])
apply (rule subset_refl)
done

end
