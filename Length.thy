(*
    File:        Length.thy
    Time-stamp:  <2016-01-06T17:48:20Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory Length imports Lambda dLambda begin

definition LLength :: "i=>i" where
"LLength(M) == LTerm_rec(%x. 0, %x m r. succ(r),
                         %m n rm rn. succ(rm Un rn), M)"

definition Length :: "i=>i" where
"Length(M) == THE n. n: (INT m: M. {LLength(m)})"


lemma LLength_eqns:
  "LLength(LVar(x)) = 0"
  "LLength(LLam(x, M)) = succ(LLength(M))"
  "LLength(LApp(M, N)) = succ(LLength(M) Un LLength(N))"
apply (unfold LLength_def)
apply simp_all
done

lemma LLength_type:
  "M: LTerm ==> LLength(M): nat"
apply (erule LTerm.induct)
apply (simp_all only: LLength_eqns)
apply (assumption | rule nat_succI nat_UnI nat_0I)+
done

lemma LSkeltonEq_imp_LLength_eq:
  assumes major: "LSkeltonEq(M, N)"
  shows "LLength(M) = LLength(N)"
apply (rule major [THEN rev_mp])
apply (rule_tac x="N" in spec)
apply (rule major [THEN LSkeltonEqD1, THEN LTerm.induct])
apply (safe elim!: LSkeltonEq_LTermEs)
apply (simp_all add: LLength_eqns)
done

lemma Length_LAQ:
  "m: LTerm ==> Length(LAQ(m)) = LLength(m)"
apply (unfold Length_def)
apply (rule the_equality)
apply (rule INT_I)
apply (rule_tac [2] not_emptyI)
apply (erule_tac [2] LAQ_self)
apply (drule LAQ_D)
apply (drule LAlphaD1 [THEN LSkeltonEq_imp_LLength_eq])
apply blast
apply (drule INT_E)
apply (erule LAQ_self)
apply (erule singletonE)
apply assumption
done

lemma Length_type:
  "M: Term ==> Length(M): nat"
apply (erule TermE)
apply hypsubst
apply (simp only: Length_LAQ)
apply (erule LLength_type)
done

lemma Length_Var:
  "x: LVariable ==> Length(Var(x)) = 0"
apply (simp add: Term_LAQ Length_LAQ LLength_eqns)
done

lemma Length_Lam:
  "[| x: LVariable; M: Term |] ==>
        Length(Lam(x, M)) = succ(Length(M))"
apply (erule TermE)+
apply (simp add: Term_LAQ Length_LAQ LLength_eqns)
done

lemma Length_App:
  "[| M: Term; N: Term |] ==>
        Length(App(M, N)) = succ(Length(M) Un Length(N))"
apply (erule TermE)+
apply (simp add: Term_LAQ Length_LAQ LLength_eqns)
done

lemmas Length_eqns = Length_Var Length_Lam Length_App

lemma Length_induct:
  assumes major: "M: Term"
  and prem:
     "!!M. [| M: Term; ALL N: Term. Length(N) < Length(M) --> P(N) |]
           ==> P(M)"
  shows "P(M)"
apply (rule major [THEN rev_mp])
apply (rule_tac P="Length(M) = Length(M)" in rev_mp)
apply (rule_tac [2] P="%x. Length(M) = Length(x) --> x : Term --> P(x)" in major [THEN [2] bspec])
apply (rule_tac [2] P="%n. ALL M: Term. n = Length(M) --> M: Term --> P(M)" in
         major [THEN Length_type, THEN complete_induct0])
apply (rule refl)
apply safe
apply (erule prem)
apply safe
apply (erule bspec [THEN bspec, THEN mp, THEN mp])
apply (erule ltD)
apply (assumption | rule refl)+
done

lemma Term_induct2:
  assumes major: "M: Term"
  and prem1: "X: Fin(LVariable)"
  and 
     "!! x . x: LVariable ==> P(Var(x))"
  and
     "!! x M . [| x: LVariable; x ~: X; M: Term; P(M) |]
          ==> P(Lam(x, M))"
  and
     "!! M N . [| M: Term; P(M); N: Term; P(N) |] ==> P(App(M, N))"
  shows "P(M)"
apply (rule major [THEN Length_induct])
apply (erule Term_cases)
apply safe
apply (rule_tac [2] prem1 [THEN [3] Infinite_LVariable_Alpha_lemma2,
          THEN bexE])
apply (erule_tac [2] asm_rl)+
apply (erule_tac [2] bexE conjE)+
apply (rotate_tac [1] 1)
apply (rotate_tac [2] 1)
apply (rotate_tac [3] 1)
prefer 2 apply simp
apply (simp_all add: Length_eqns)
apply (rule_tac [3] assms)
apply (rule_tac [2] assms)
apply (rule_tac [1] assms)
prefer 5
prefer 6
prefer 8
apply assumption+
apply (erule_tac [3] bspec [THEN mp])
apply (erule_tac [2] bspec [THEN mp])
apply (erule_tac [1] bspec [THEN mp])
apply (assumption | rule nat_into_Ord le_refl Length_type
         Un_upper1_le Un_upper2_le)+
done

lemmas Term_typechecks = Term_intros subst_type Length_type
lemmas Term_simps = Term_free_iffs Length_eqns subst_eqns FV_eqns

declare Term_typechecks [TC]
declare Term_simps [simp]

end
