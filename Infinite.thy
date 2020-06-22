(*
    File:        Infinite.thy
    Time-stamp:  <2020-06-22T04:22:53Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory Infinite imports ZF.Finite ZF.Cardinal begin

definition Infinite :: "i => o" where
  "Infinite(X) == ALL F: Fin(X). X ~= F"

lemma InfiniteI:
  "[| !! x. [| x: Fin(X); x = X |] ==> False |] ==> Infinite(X)"
apply (unfold Infinite_def)
apply blast
done
  
lemma InfiniteI2:
  "X ~: Fin(X) ==> Infinite(X)"
apply (unfold Infinite_def)
apply blast
done

lemma Infinite_imp_not_empty:
  "Infinite(X) ==> X ~= 0"
apply (unfold Infinite_def)
apply (drule bspec)
by (rule Fin.intros)

lemma neq_subset_imp_bex_not_mem:
  "[| A ~= B; B <= A |] ==> EX x: A. x ~: B"
apply (rule swap)
apply (erule contrapos)
apply (rule equalityI)
apply (assumption, assumption)
apply (rule subsetI)
apply (rule swap)
apply (rule_tac [2] bexI)
apply assumption+
done

lemma InfiniteD:
  "[| Infinite(X); F: Fin(X) |] ==> EX x: X. x ~: F"
apply (unfold Infinite_def)
(* apply blast *)
apply (drule bspec)
apply assumption
apply (drule FinD)
apply (erule neq_subset_imp_bex_not_mem)
apply assumption
done

lemmas InfiniteE = InfiniteD [THEN bexE]

lemma Infinite_not_Finite_iff: "Infinite(X) <-> ~ Finite(X)"
apply (simp add: Infinite_def Finite_Fin_iff)
apply blast
done

end
