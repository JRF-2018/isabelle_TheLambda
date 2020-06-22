(*
    File:        LAlpha.thy
    Time-stamp:  <2016-01-12T14:58:28Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory LAlpha imports LLambda Infinite begin

definition LAV :: "i => i" where
"LAV(M) == {x: LVariable. EX l. <l, TLVar(x)>: LOcc(M) |
                   <l, TLLam(x)>: LOcc(M)}"

definition LSkeltonEq :: "[i, i] => o" where
"LSkeltonEq(M, N) == M: LTerm & N: LTerm &
   (ALL l. (EX x. <l, TLVar(x)>: LOcc(M))
                    <-> (EX x. <l, TLVar(x)>: LOcc(N))) &
   (ALL l. (EX x. <l, TLLam(x)>: LOcc(M))
                    <-> (EX x. <l, TLLam(x)>: LOcc(N))) &
   (ALL l. <l, TLApp>: LOcc(M) <-> <l, TLApp>: LOcc(N))"

definition LAlpha :: "[i, i]=>o" where
"LAlpha(M, N) == LSkeltonEq(M, N) &
   (ALL u. LFreeIn(u, M) <-> LFreeIn(u, N)) &
   (ALL l m. (EX T U. LBoundBy(<l, T>, <m, U>, M))
                     <-> (EX T U. LBoundBy(<l, T>, <m, U>, N)))"


(** LAV **)
lemma LAV_I1:
  "[| <l, TLVar(x)>: LOcc(M); M: LTerm |] ==> x: LAV(M)"
apply (unfold LAV_def)
apply (frule LOcc_typeD2)
apply assumption
apply (blast elim!: LTag_typeEs)
done

lemma LAV_I2:
  "[| <l, TLLam(x)>: LOcc(M); M: LTerm |] ==> x: LAV(M)"
apply (unfold LAV_def)
apply (frule LOcc_typeD2)
apply assumption
apply (blast elim!: LTag_typeEs)
done

lemma LAV_E:
  "[| x: LAV(M);
    !!l. [| <l, TLVar(x)>: LOcc(M); x: LVariable |]
        ==> R;
    !!l. [| <l, TLLam(x)>: LOcc(M); x: LVariable |]
        ==> R
   |] ==> R"
apply (unfold LAV_def)
apply blast
done

lemma LAV_LVar:
  "x: LVariable ==> LAV(LVar(x)) = {x}"
apply (unfold LAV_def)
apply (rule equalityI)
apply (blast elim!: LOcc_LTermEs LTag.free_elims
             intro: LOcc_LTermIs)+
done

lemma LAV_LLam:
  "x: LVariable ==> LAV(LLam(x, M)) = cons(x, LAV(M))"
apply (unfold LAV_def)
apply (rule equalityI)
apply (blast elim!: LOcc_LTermEs LTag.free_elims
             intro: LOcc_LTermIs)+
done

lemma LAV_LApp:
  "LAV(LApp(M, N)) = LAV(M) Un LAV(N)"
apply (unfold LAV_def)
apply (rule equalityI)
apply (blast elim!: LOcc_LTermEs LTag.free_elims
             intro: LOcc_LTermIs)+
done

lemmas LAV_eqns = LAV_LVar LAV_LLam LAV_LApp
declare LAV_eqns [simp]

lemmas LTerm_Occ_ind_cond_Occ_FinI = Occ_ind_cond_Occ_FinI [OF
  LTerm_Occ_ind_cond]

lemma LAV_Fin:
  "M: LTerm ==> LAV(M): Fin(LVariable)"
apply (unfold LAV_def)
apply (erule LTerm_Occ_ind_cond_Occ_FinI [THEN Fin_induct])
apply simp
apply (erule SigmaE)
apply (erule LTag.cases)
apply hypsubst
apply (rule_tac P="%x. x: Fin(LVariable)" in ssubst)
apply (erule_tac [2] Fin.intros)
prefer 2 apply assumption
apply (rule_tac [2] P="%x. x: Fin(LVariable)" in ssubst)
apply (erule_tac [3] Fin.intros)
prefer 3 apply assumption
apply (rule_tac [3] P="%x. x: Fin(LVariable)" in ssubst)
prefer 4 apply assumption
apply (rule equalityI,
       blast elim!: LTag.free_elims,
       blast elim!: LTag.free_elims)+
done

lemma LFV_subset_LAV:
  "M: LTerm ==> LFV(M) <= LAV(M)"
apply (erule LTerm.induct)
apply simp_all
apply blast+
done

(** LSkeltonEq **)
lemma LSkeltonEqD1:
  "LSkeltonEq(M, N) ==> M: LTerm"
apply (unfold LSkeltonEq_def)
apply (erule conjunct1)
done

lemma LSkeltonEqD2:
  "LSkeltonEq(M, N) ==> N: LTerm"
apply (unfold LSkeltonEq_def)
apply (erule conjunct2 [THEN conjunct1])
done

lemma LSkeltonEq_TLVarD:
  "[| LSkeltonEq(M, N); <l, TLVar(x)>: LOcc(M) |]
      ==> EX x. <l, TLVar(x)>: LOcc(N)"
apply (unfold LSkeltonEq_def)
apply blast
done

lemma LSkeltonEq_TLLamD:
  "[| LSkeltonEq(M, N); <l, TLLam(x)>: LOcc(M) |]
      ==> EX x. <l, TLLam(x)>: LOcc(N)"
apply (unfold LSkeltonEq_def)
apply blast
done

lemma LSkeltonEq_TLAppD:
  "[| LSkeltonEq(M, N); <l, TLApp>: LOcc(M) |]
      ==> <l, TLApp>: LOcc(N)"
apply (unfold LSkeltonEq_def)
apply blast
done

lemma LSkeltonEq_refl:
  "M: LTerm ==> LSkeltonEq(M, M)"
apply (unfold LSkeltonEq_def)
apply blast
done

lemma LSkeltonEq_sym:
  "LSkeltonEq(M, N) ==> LSkeltonEq(N, M)"
apply (unfold LSkeltonEq_def)
apply blast
done

lemma LSkeltonEq_trans:
  "[| LSkeltonEq(M, N); LSkeltonEq(N, L) |] ==> LSkeltonEq(M, L)"
apply (unfold LSkeltonEq_def)
apply blast
done

lemma LSkeltonEq_LVarI:
  "[| x: LVariable; y: LVariable |] ==> LSkeltonEq(LVar(x), LVar(y))"
apply (unfold LSkeltonEq_def)
apply (blast elim!: LOcc_LTermEs LTag.free_elims
        intro: LOcc_LTermIs)
done

lemma LSkeltonEq_LLamI:
  "[| x: LVariable; y: LVariable;  LSkeltonEq(M, N) |]
      ==> LSkeltonEq(LLam(x, M), LLam(y, N))"
apply (unfold LSkeltonEq_def)
apply (blast elim!: LOcc_LTermEs LTag.free_elims
        intro: LOcc_LTermIs)
done

lemma LSkeltonEq_LAppI:
"[| LSkeltonEq(A, C); LSkeltonEq(B, D)|]
    ==> LSkeltonEq(LApp(A, B), LApp(C, D))"
apply (unfold LSkeltonEq_def)
apply (elim conjE)
apply (intro LTerm.intros conjI)
apply assumption+
apply (blast elim!: LOcc_LTermEs LTag.free_elims
        intro: LOcc_LTermIs)+
done

lemmas LSkeltonEq_LTermIs = LSkeltonEq_LVarI LSkeltonEq_LLamI
                            LSkeltonEq_LAppI

lemma LSkeltonEq_LVarE:
  assumes major: "LSkeltonEq(LVar(x), N)"
  and prem: "!! y B. [| N = LVar(y); x: LVariable; y: LVariable |] ==> R"
  shows "R"
apply (insert major)
apply (unfold LSkeltonEq_def)
apply (elim LTerm_typeEs conjE)
apply (subgoal_tac "EX y. <[], TLVar(y)>: LOcc(N)"
                   "EX y: LVariable.  N = LVar(y)")
prefer 3
apply (erule spec [THEN iffD1])
apply (assumption | rule exI LOcc_LTermIs)+
prefer 2
apply (erule exE)
apply (erule_tac a="N" in LTerm.cases)
prefer 3
apply hypsubst
apply (blast elim!: LTag.free_elims list.free_elims LOcc_LTermEs)
prefer 2
apply (blast elim!: LTag.free_elims list.free_elims LOcc_LTermEs)
apply (assumption | rule bexI)+
apply (erule bexE)
apply (rule prem)
apply assumption+
done

lemma LSkeltonEq_LLamE:
  assumes major: "LSkeltonEq(LLam(x, A), N)"
  and prem:
     "!! y B. [| N = LLam(y, B); x: LVariable; y: LVariable;
        LSkeltonEq(A, B) |] ==> R"
  shows "R"
apply (insert major)
apply (unfold LSkeltonEq_def)
apply (elim LTerm_typeEs conjE)
apply (subgoal_tac "EX y. <[], TLLam(y)>: LOcc(N)"
          "EX y: LVariable.  EX B: LTerm. N = LLam(y, B)")
prefer 3
apply (erule spec [THEN iffD1])
apply (assumption | rule exI LOcc_LTermIs)+
prefer 2
apply (erule exE)
apply (erule_tac a="N" in LTerm.cases)
apply hypsubst
apply (blast elim!: LTag.free_elims LOcc_LTermEs)
prefer 2
apply (blast elim!: LTag.free_elims LOcc_LTermEs list.free_elims)
apply (assumption | rule bexI)+
apply (elim bexE exE)
apply hypsubst
apply (rule prem)
apply assumption+
apply (unfold LSkeltonEq_def)
apply (intro conjI)
apply assumption+

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)

apply (intro allI iffI)
apply (drule spec [THEN iffD1], erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)
apply (drule spec [THEN iffD2], erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)

done

lemma LSkeltonEq_LAppE:
  assumes major: "LSkeltonEq(LApp(A, B), N)"
  and prem:
     "!! C D. [| N = LApp(C, D); LSkeltonEq(A, C); LSkeltonEq(B, D) |]
            ==> R"
  shows "R"
apply (insert major)
apply (unfold LSkeltonEq_def)
apply (elim LTerm_typeEs conjE)
apply (subgoal_tac "<[], TLApp>: LOcc(N)"
                   "EX C: LTerm.  EX D: LTerm. N = LApp(C, D)")
prefer 3
apply (erule spec [THEN iffD1])
apply (assumption | rule LOcc_LTermIs)+
prefer 2
apply (erule_tac a="N" in LTerm.cases)
apply hypsubst
apply (blast elim!: LTag.free_elims LOcc_LTermEs)
apply (blast elim!: LTag.free_elims list.free_elims LOcc_LTermEs)
apply (assumption | rule bexI)+

apply (elim bexE)
apply (rule prem)
apply assumption
apply (unfold LSkeltonEq_def)

apply hypsubst
apply (intro conjI)
apply assumption+

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)

apply (intro allI iffI)
apply (drule spec [THEN iffD1], erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)
apply (drule spec [THEN iffD2], erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)

apply hypsubst
apply (intro conjI)
apply assumption+

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)

apply (intro allI iffI)
apply (drule spec [THEN iffD1], erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)
apply (drule spec [THEN iffD2], erule LOcc_LTermIs)
apply (blast elim!: list.free_elims LTag.free_elims LOcc_LTermEs)

done

lemmas LSkeltonEq_LTermEs = LSkeltonEq_LVarE LSkeltonEq_LLamE
                          LSkeltonEq_LAppE

lemma LSkeltonEq_Lsubst_LVar:
  "[| M: LTerm; y: LVariable |] ==> LSkeltonEq(M, Lsubst(M, x, LVar(y)))"
apply (unfold LSkeltonEq_def Lsubst_def Lgraft_def)
apply (subgoal_tac "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(LVar(y))):
                     Occ_range(LTag, LArity)")
prefer 2
apply (assumption | rule LTerm.intros LTerm_Occ_Graft_in_Occ_range2 
         LOcc_in_Occ_range Incomparable_LFO domain_mono LFO_subset_LOcc)+
apply (assumption | rule conjI LTerm_def_Occinv_type)+
apply (rule_tac [2] conjI)
apply (simp_all only: LTerm_def_Occ_Occinv)
apply (rule_tac [3] iffI allI)+
apply (rule_tac [2] iffI allI)+
apply (rule_tac [1] iffI allI)+
apply (erule_tac [4] exE)
apply (erule_tac [3] exE)
apply (erule_tac [2] exE)
apply (erule_tac [1] exE)
apply (case_tac "<l, TLVar(xa)>: LFO(x, M)")
prefer 2

apply (safe elim!: LOcc_LTermEs LTag.free_elims
        LOcc_domain [THEN [2] Occ_GraftE] Occ_ShiftE LFO_E)
apply (erule_tac [4] LFreeInE2)
apply (frule_tac [4] LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 4 apply assumption
prefer 4 apply simp
apply (erule exI)
prefer 3 apply (erule exI)
prefer 4 apply (erule exI)
apply (rule_tac [3] exI)
apply (rule_tac [2] exI)
apply (rule_tac [1] exI)
apply (rule_tac [4] Occ_GraftI1)
apply (rule_tac [3] Occ_GraftI1)
apply (rule_tac [2] Occ_GraftI2)
apply (rule_tac [1] Occ_GraftI1)
prefer 5
prefer 7
apply assumption+
apply (erule_tac [2] LFO_I [THEN domainI])
apply (rule_tac [2] P="%x. <x, TLVar(y)>: Occ_Shift(la, LOcc(LVar(y)))"
          in app_right_Nil [THEN subst])
apply (rule_tac [3] Occ_ShiftI)
apply (erule_tac [2] LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 2
prefer 3
apply (assumption | rule LOcc_LTermIs)+

apply (safe elim!: LTag.free_elims LFO_E LFreeInE2)

apply (rule_tac LOcc_in_Occ_range [THEN Occ_rangeE], assumption)
apply (subgoal_tac "la = l")
apply (erule_tac [2] DenseTree_CorrectArity_0D)
prefer 3
prefer 4
prefer 5
apply assumption+
prefer 2
apply (drule_tac x="TLVar(x)" in bspec)
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD2])
apply assumption
apply simp
apply hypsubst
apply (subgoal_tac "TLVar(xa) = TLVar(x)")
apply (erule_tac [2] functionalD)
apply (clarify elim!: LTag.free_elims)
apply (erule notE)
apply (rule LFreeInI [THEN LFO_I])
apply (erule_tac [3] spec [THEN mp, THEN notE])
apply assumption+

apply (rule_tac LOcc_in_Occ_range [THEN Occ_rangeE], assumption)
apply (subgoal_tac "la = l")
apply (erule_tac [2] DenseTree_CorrectArity_0D)
prefer 3
prefer 4
prefer 5
apply assumption+
prefer 2
apply (drule_tac x="TLVar(x)" in bspec)
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD2])
apply assumption
apply simp
apply hypsubst
apply (subgoal_tac "TLLam(xa) = TLVar(x)")
apply (erule_tac [2] functionalD)
apply (clarify elim!: LTag.free_elims)
apply assumption+

apply (rule_tac LOcc_in_Occ_range [THEN Occ_rangeE], assumption)
apply (subgoal_tac "la = l")
apply (erule_tac [2] DenseTree_CorrectArity_0D)
prefer 3
prefer 4
prefer 5
apply assumption+
prefer 2
apply (drule_tac x="TLVar(x)" in bspec)
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD2])
apply assumption
apply simp
apply hypsubst
apply (subgoal_tac "TLApp = TLVar(x)")
apply (erule_tac [2] functionalD)
apply (clarify elim!: LTag.free_elims)
apply assumption+

done

(** LAlpha **)
lemma LAlphaD1:
  "LAlpha(M, N) ==> LSkeltonEq(M, N)"
apply (unfold LAlpha_def)
apply (erule conjunct1)
done

lemma LAlphaD2:
  "[| LAlpha(M, N); LFreeIn(u, M) |] ==> LFreeIn(u, N)"
apply (unfold LAlpha_def)
apply (erule conjunct2 [THEN conjunct1, THEN spec, THEN iffD1])
apply assumption
done

lemma LAlphaD3:
  "[| LAlpha(M, N); LBoundBy(<l, T>, <m, U>, M) |]
      ==> EX x. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, N)"
apply (unfold LAlpha_def)
apply (frule conjunct2 [THEN conjunct2])
apply (drule spec [THEN spec, THEN iffD1])
apply (rule exI [THEN exI])
apply assumption
apply (elim exE)
apply (rule_tac M="N" in LBoundByE)
apply assumption
apply blast
done

lemma LAlphaI:
  assumes prem1: "LSkeltonEq(M, N)"
  and prem2:
      "!! l x. LFreeIn(<l, TLVar(x)>, M) <-> LFreeIn(<l, TLVar(x)>, N)"
  and prem3: 
      "!! l m. (EX x. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, M))
               <-> (EX x. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, N))"
  shows "LAlpha(M, N)"
apply (unfold LAlpha_def)
apply (rule prem1 [THEN conjI])
apply safe

apply (rule LFreeInE)
apply assumption
apply hypsubst
apply (erule_tac prem2 [THEN iffD1])
apply (rule LFreeInE)
apply assumption
apply hypsubst
apply (erule_tac prem2 [THEN iffD2])

apply (rule LBoundByE)
apply assumption
apply safe
apply (drule_tac exI [THEN prem3 [THEN iffD1]])
apply blast
apply (rule LBoundByE)
apply assumption
apply safe
apply (drule_tac exI [THEN prem3 [THEN iffD2]])
apply blast

done

lemma LAlphaI2:
  assumes "M: LTerm"
  and "N: LTerm"
  and "!! l. (EX x. <l, TLLam(x)>: LOcc(M)) <->
                            (EX x. <l, TLLam(x)>: LOcc(N))"
  and "!! l. <l, TLApp>: LOcc(M) <-> <l, TLApp>: LOcc(N)"
  and prem1: "!! l x. LFreeIn(<l, TLVar(x)>, M) <-> LFreeIn(<l, TLVar(x)>, N)"
  and prem2: "!! l m. (EX x. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, M))
               <-> (EX x. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, N))"
  shows "LAlpha(M, N)"
apply (rule LAlphaI)
defer 1
apply (assumption | rule assms)+
apply (unfold LSkeltonEq_def)
apply (assumption | rule assms conjI)+
prefer 2
apply (assumption | rule assms allI conjI)+
apply safe
apply (drule_tac [2] TLVar_free_or_bound)
apply (drule_tac [1] TLVar_free_or_bound)
apply (rule assms)
prefer 2 apply (rule assms)
apply (safe elim!: LBoundInE LBinding_imp_LBoundByE)
apply (drule_tac [1] prem1 [THEN iffD1])
apply (drule_tac [3] prem1 [THEN iffD2])
apply (drule_tac [2] exI [THEN prem2 [THEN iffD1]])
apply (drule_tac [4] exI [THEN prem2 [THEN iffD2]])
apply (safe elim!: LBoundByE2 LBindingE2 LFreeInE2)
apply (erule exI)+
done

lemma LAlpha_refl:
  "M: LTerm ==> LAlpha(M, M)"
apply (unfold LAlpha_def)
apply (blast intro: LSkeltonEq_refl)
done

lemma LAlpha_sym:
  "LAlpha(M, N) ==> LAlpha(N, M)"
apply (unfold LAlpha_def)
apply (blast intro: LSkeltonEq_sym)
done

lemma LAlpha_trans:
  "[| LAlpha(M, N); LAlpha(N, L) |] ==> LAlpha(M, L)"
apply (unfold LAlpha_def)
apply (blast intro: LSkeltonEq_trans)
done

lemma LAlpha_LVarI:
  "x: LVariable ==> LAlpha(LVar(x), LVar(x))"
apply (rule LAlpha_refl)
apply (assumption | rule LTerm.intros)+
done

lemma LAlpha_LLamI1:
  "[| LAlpha(M, N); x: LVariable |]
       ==> LAlpha(LLam(x, M), LLam(x, N))"
apply (unfold LAlpha_def)
apply (elim conjE)
apply (frule LSkeltonEqD1)
apply (frule LSkeltonEqD2)
apply (assumption | rule LSkeltonEq_LLamI conjI)+
apply (rule iffI [THEN allI])
apply (erule_tac [2] LFreeIn_LTermEs)
apply (erule LFreeIn_LTermEs)
apply (drule spec [THEN iffD1], assumption)
apply hypsubst
prefer 2
apply (drule spec [THEN iffD2], assumption)
apply hypsubst
prefer 2
apply ((erule notE, erule sym) 
      | (assumption | rule LFreeIn_LTermIs notI))+

apply (rule iffI [THEN allI, THEN allI])
apply (safe elim!: LBoundBy_LTermEs LTag.free_elims)

prefer 4 apply (drule spec [THEN spec, THEN iffD2], erule exI [THEN exI])
apply (elim exE)
prefer 4 apply (drule spec [THEN iffD2], assumption)
prefer 4 apply (drule spec [THEN spec, THEN iffD1], erule exI [THEN exI])
apply (elim exE)
prefer 4 apply (drule spec [THEN iffD1], assumption)
apply (assumption | rule LBoundBy_LTermIs exI)+
done

lemma LAlpha_LLamI2:
  "[| LAlpha(M, Lsubst(N, y, LVar(x))); LFreeForIn(LVar(x), y, N);
     x ~: LFV(N) |]
       ==> LAlpha(LLam(x, M), LLam(y, N))"
apply (unfold LAlpha_def)
apply (elim conjE)
apply (subgoal_tac "x: LVariable" "y: LVariable" "N: LTerm")
prefer 2
prefer 3
prefer 4
apply (erule LFreeForInE, erule LTerm_typeEs, assumption)+
apply (rule conjI)
apply (rule LSkeltonEq_LLamI)
apply assumption+
apply (rule LSkeltonEq_trans)
apply (rule_tac [2] LSkeltonEq_Lsubst_LVar [THEN LSkeltonEq_sym])
apply assumption+

apply (frule LSkeltonEqD1)
apply (rule conjI)
apply (rule_tac [2] iffI [THEN allI, THEN allI])
apply (rule iffI [THEN allI])
apply (safe elim!: LBoundBy_LTermEs LFreeIn_LTermEs)
apply (subgoal_tac [2] "x ~= ya")
prefer 3
apply (rule notI)
apply hypsubst
apply (erule notE, erule LFV_I)
prefer 2
apply (drule LFreeIn_LsubstI1)
apply assumption+
apply (drule spec [THEN iffD2], assumption)
prefer 2

apply (subgoal_tac [5] "ma: list(nat)"
          "LFreeIn(<ma @ [], TLVar(x)>, Lsubst(N, y, LVar(x)))")
apply (erule_tac [7] LFreeInE2)
apply (rule_tac [7] LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 8 apply assumption
prefer 7 apply assumption
prefer 6
apply (rule LFreeIn_LsubstI2)
apply (assumption | rule LFreeIn_LVarI LFO_I)+
prefer 5
apply (simp only: app_right_Nil)
apply (drule spec [THEN iffD2], assumption)
defer 1
defer 5

prefer 6
apply (drule LBoundBy_LsubstI1)
apply (drule_tac [2] spec [THEN spec, THEN iffD2],
       erule_tac [2] exI [THEN exI])
apply (assumption | rule LTerm.intros)+
apply (elim exE)
defer 1

prefer 4 apply (drule spec [THEN spec, THEN iffD1], erule exI [THEN exI])
apply (elim exE)
prefer 4 apply (drule spec [THEN iffD1], assumption)
prefer 4
prefer 4 apply (drule spec [THEN iffD1], assumption)

apply (frule_tac [4] u="<ma, Ta>" in LBoundByD1)
apply (erule_tac [4] LBindingE)
apply (safe elim!: LFreeIn_LTermEs LFO_E2 LBoundBy_LTermEs
        LTag.free_elims LFreeIn_LsubstE LBoundBy_LsubstE)
apply (rule_tac [3] exI [THEN exI])
apply (rule_tac [4] exI [THEN exI])
apply (rule_tac [5] exI [THEN exI])
apply (rule_tac [6] exI [THEN exI])
apply (rule_tac [7] exI [THEN exI])
apply (rule_tac [8] exI [THEN exI])
apply (rule_tac [8] LFreeIn_LTermIs LBoundBy_LTermIs)
apply (rule_tac [7] LFreeIn_LTermIs LBoundBy_LTermIs)
apply (rule_tac [6] LFreeIn_LTermIs LBoundBy_LTermIs)
apply (rule_tac [5] LFreeIn_LTermIs LBoundBy_LTermIs)
apply (rule_tac [4] LFreeIn_LTermIs LBoundBy_LTermIs)
apply (rule_tac [3] LFreeIn_LTermIs LBoundBy_LTermIs)
apply (rule_tac [2] LFreeIn_LTermIs LBoundBy_LTermIs)
apply (rule_tac [1] LFreeIn_LTermIs LBoundBy_LTermIs)
prefer 3
prefer 4
prefer 6
prefer 9
prefer 10
prefer 11
prefer 13
prefer 14
apply assumption+
prefer 4
apply (subgoal_tac "n: list(nat)")
apply (simp only: app_right_Nil)
apply (erule LFreeInE2)+
apply (rule LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption
apply (blast intro: LFV_I)+ 
done

lemma LAlpha_LAppI:
  "[| LAlpha(A, C); LAlpha(B, D) |] ==> LAlpha(LApp(A, B), LApp(C, D))"
apply (unfold LAlpha_def)
apply (elim conjE)
apply (rule conjI)
apply (erule LSkeltonEq_LAppI)
apply assumption
apply (subgoal_tac "A: LTerm" "B: LTerm" "C: LTerm" "D: LTerm")
defer 1
apply (erule LSkeltonEqD1 LSkeltonEqD2)+
apply (rule conjI)
apply (rule_tac [2] iffI [THEN allI, THEN allI])
apply (rule iffI [THEN allI])
apply (safe elim!: LFreeIn_LTermEs LBoundBy_LTermEs)

prefer 8 apply (drule spec [THEN spec, THEN iffD2], erule exI [THEN exI])
apply (elim exE)
apply (intro exI)
prefer 8 apply (drule spec [THEN spec, THEN iffD2], erule exI [THEN exI])
apply (elim exE)
apply (intro exI)
prefer 8 apply (drule spec [THEN spec, THEN iffD1], erule exI [THEN exI])
apply (elim exE)
apply (intro exI)
prefer 8 apply (drule spec [THEN spec, THEN iffD1], erule exI [THEN exI])
apply (elim exE)
apply (intro exI)
prefer 8 apply (drule spec [THEN iffD2], assumption)
prefer 8 apply (drule spec [THEN iffD2], assumption)
prefer 8 apply (drule spec [THEN iffD1], assumption)
prefer 8 apply (drule spec [THEN iffD1], assumption)

apply (rule LFreeIn_LTermIs LBoundBy_LTermIs, assumption+)+
done

lemmas LAlpha_LTermIs = LAlpha_LVarI LAlpha_LLamI1 
                      LAlpha_LLamI2 LAlpha_LAppI

lemma LFreeForIn_name_change:
  assumes prem1: "LFreeForIn(LVar(y), x, M)"
  and prem2: "LFreeForIn(N, x, M)"
  and prem3: "y ~: LFV(M)"
  shows "LFreeForIn(N, y, Lsubst(M, x, LVar(y)))"
apply (rule prem1 [THEN LFreeForInE])
apply (rule prem2 [THEN LFreeForInE])
apply (insert prem3)
apply (rule LFreeForInI)
apply (safe elim!: LTerm_typeEs LOcc_LsubstE LFreeIn_LsubstE LFO_E
                   LOcc_LTermEs LTag.free_elims LFreeIn_LTermEs
            intro!: Lsubst_type)
apply (erule notE, erule LFV_I)
apply (erule spec [THEN spec, THEN spec, THEN mp], erule conjI)
apply safe
prefer 3 apply assumption
prefer 2 apply assumption
apply (subgoal_tac "n: list(nat)")
prefer 2
apply (erule LFreeInE2)
apply (erule LOcc_typeD1)
apply assumption
apply (simp only: app_right_Nil)
done

lemma LFV_Lsubst_notI:
  "[| x ~= y; x: LVariable; M: LTerm |]
       ==> y ~: LFV(Lsubst(M, y, LVar(x)))"
apply (rule notI)
apply (safe elim!: LFreeIn_LsubstE LFO_E LFV_E LFreeIn_LTermEs
           LTag.free_elims)
done

lemma LAlpha_LLamI3:
  "[| LAlpha(M, N); LFreeForIn(LVar(y), x, N); y ~: LFV(N) |]
       ==> LAlpha(LLam(x, M), LLam(y, Lsubst(N, x, LVar(y))))"
apply (frule LFreeForInD1)
apply (erule LTerm_typeEs)
apply (frule LFreeForInD2)
apply (frule LAlphaD1 [THEN LSkeltonEqD2])
apply (case_tac "y = x")
apply hypsubst
apply (rule LAlpha_LLamI1)
apply (simp add: Lsubst_self)
apply assumption
apply (rule LAlpha_LLamI2)
apply (simp add: Lsubst_lemma2 Lsubst_self)
apply (assumption | rule LFV_Lsubst_notI LFreeForIn_left_LVarI
         LFreeForIn_name_change)+
done

lemma Infinite_LVariable_LAlpha_lemma:
  assumes infv: "Infinite(LVariable)"
  and major: "M: LTerm"
  shows 
    "[| x: LVariable; N: LTerm |] ==>
       EX M': LTerm. LAlpha(M, M') & LFreeForIn(N, x, M')"
apply (rule major [THEN LTerm.induct])
apply (rule bexI)
apply (assumption | rule LAlpha_LTermIs LFreeForIn_LTermIs
         LTerm.intros conjI)+
apply safe
apply (rule_tac F="cons(xa, LAV(N) Un LAV(M'))" in infv [THEN InfiniteE])
apply (assumption | rule Fin.intros LAV_Fin Fin_UnI)+
apply (rule_tac x="LLam(xaa, Lsubst(M', xa, LVar(xaa)))" in bexI)
prefer 2
apply (assumption | rule LTerm.intros Lsubst_type)+
apply (subgoal_tac "xaa ~: LFV(M')" "LFreeForIn(LVar(xaa), xa, M')")
apply safe
prefer 4 apply (blast intro: LFV_subset_LAV [THEN subsetD])
apply (erule_tac [3] swap, rule_tac [3] LFreeForInI)
prefer 6 apply (blast elim!: LFV_E LFreeIn_LTermEs LTag.free_elims
                      intro: LAV_I2)
apply (rule LAlpha_LLamI2)
apply (simp add: Lsubst_self Lsubst_lemma2)
apply (rule LFreeForIn_name_change)
apply (rule_tac [4] LFV_Lsubst_notI)
apply (assumption | rule LFreeForIn_left_LVarI)+
apply (rule LFreeForInI)
prefer 5
prefer 6
prefer 7
prefer 8
apply (assumption | rule conjI bexI LAlpha_LTermIs LFreeForIn_LTermIs
         LTerm.intros Lsubst_type)+
apply (safe elim!: LFV_E LFreeIn_LsubstE LFO_E2
                 LFreeForInE LOcc_LsubstE initseg_left_ConsE
                 list.free_elims LOcc_LTermEs LFreeIn_LTermEs
                 LTag.free_elims)
apply (erule LFreeInE2)+
apply (erule notE, erule LAV_I1)
apply assumption
apply (erule spec [THEN spec, THEN spec, THEN mp], intro conjI)
prefer 2 apply assumption
apply (assumption | rule LFV_I)+
done

lemma Infinite_LVariable_LAlpha_lemma2:
  assumes infv:  "Infinite(LVariable)"
  and major: "M: LTerm"
  shows
    "[| x: LVariable; X: Fin(LTerm) |] ==>
       EX M': LTerm. LAlpha(M, M') & (ALL N: X. LFreeForIn(N, x, M'))"
apply (rule major [THEN LTerm.induct])
apply (rule bexI)
apply ((assumption | rule LAlpha_LTermIs LFreeForIn_LTermIs
         LTerm.intros conjI ballI)
       | (drule Fin.dom_subset [THEN subsetD, THEN PowD],
          erule subsetD))+
apply safe
apply (rule_tac F="cons(xa, (UN N: X. LAV(N)) Un LAV(M'))" in
         infv [THEN InfiniteE])
apply (assumption | rule Fin.intros LAV_Fin Fin_UnI Fin_UnionI
        Fin_RepFunI)+

apply (rule_tac x="LLam(xaa, Lsubst(M', xa, LVar(xaa)))" in bexI)
prefer 2
apply (assumption | rule LTerm.intros Lsubst_type)+
apply (subgoal_tac "xaa ~: LFV(M')" "LFreeForIn(LVar(xaa), xa, M')")
apply safe
prefer 4 apply (blast intro!: LFV_subset_LAV [THEN subsetD])
apply (erule_tac [3] swap, rule_tac [3] LFreeForInI)
prefer 6 apply (blast elim!: LFV_E LFreeIn_LTermEs LTag.free_elims
                 intro: LAV_I2)
apply (rule LAlpha_LLamI2)
apply (simp add: Lsubst_self Lsubst_lemma2)
apply (rule LFreeForIn_name_change)
apply (rule_tac [4] LFV_Lsubst_notI)
apply (assumption | rule LFreeForIn_left_LVarI)+
apply (rule LFreeForInI)
defer 4
apply ((assumption | rule conjI Lsubst_type bexI LFV_I ballI
          LAlpha_LTermIs LFreeForIn_LAppI LTerm.intros)
       | (drule Fin.dom_subset [THEN subsetD, THEN PowD],
          erule subsetD)
       | (erule bspec))+
apply (safe elim!: LFV_E LFreeIn_LsubstE LFO_E2 LFreeForInE
        LOcc_LsubstE initseg_left_ConsE list.free_elims
        LOcc_LTermEs LFreeIn_LTermEs LTag.free_elims)
apply (erule LFreeInE2)+
apply (erule swap, rule UnionI)
apply (rule RepFunI)
apply assumption
apply (erule LAV_I1)
apply assumption
apply (drule bspec, assumption)
apply (erule LFreeForInE)
apply (erule spec [THEN spec, THEN spec, THEN mp], intro conjI,
       erule_tac [2] asm_rl)
prefer 2 apply assumption
apply (assumption | rule LFV_I)+
done

lemma LAlpha_LVarE:
  assumes major: "LAlpha(LVar(x), N)"
  and prem: "[| N = LVar(x); x: LVariable |] ==> R"
  shows "R"
apply (insert major)
apply (unfold LAlpha_def)
apply (rule prem)
apply (safe elim!: LSkeltonEq_LVarE)
apply (drule spec [THEN iffD1])
apply (rule LFreeIn_LTermIs)
apply (erule_tac [2] LFreeIn_LTermEs)
apply (safe elim!: LTag.free_elims)
done

lemma LAlpha_LLamE:
  assumes infv: "Infinite(LVariable)"
  and major: "LAlpha(LLam(x, M), N)"
  and prem1:
     "!! N'. [| N = LLam(x, N'); LAlpha(M, N') |] ==> R"
  and prem2:
     "!! y M' N'. [| N = LLam(y, N'); LAlpha(M, M');
                   LFreeForIn(LVar(y), x, M'); y ~: LFV(M');
                   LAlpha(N', Lsubst(M', x, LVar(y)))
      |] ==> R"
  shows "R"
apply (insert major)
apply (unfold LAlpha_def)
apply safe
apply (erule LSkeltonEq_LLamE)
apply (frule LSkeltonEqD1)
apply (frule LSkeltonEqD2)
apply (case_tac "x = y")
apply hypsubst
prefer 2
apply (rule_tac [2] prem1)
apply (rule_tac [1] M1="M" and N1="LVar(y)" and x1="x" in
        infv [THEN Infinite_LVariable_LAlpha_lemma, THEN bexE])
apply (assumption | rule LTerm.intros)+
apply (erule conjE)
apply (rule prem2)
prefer 6
apply assumption+
apply (unfold LAlpha_def)
apply (safe elim!: LFV_E)
apply (drule spec [THEN iffD2], assumption)
apply (drule spec [THEN iffD1], rule LFreeIn_LLamI)
apply assumption
apply (safe elim!: LFreeIn_LTermEs LTag.free_elims)
apply (erule LSkeltonEq_sym [THEN LSkeltonEq_trans])
apply (erule LSkeltonEq_trans)
apply (assumption | rule LSkeltonEq_Lsubst_LVar)+

apply (rule LFreeInE)
apply assumption
apply hypsubst
apply (case_tac "xaa = y")
apply hypsubst
prefer 2
apply (drule spec [THEN iffD2], erule LFreeIn_LLamI)
apply assumption+
apply (clarify elim!: LFreeIn_LTermEs list.free_elims LTag.free_elims)
apply (drule spec [THEN iffD1], assumption)
apply (rule LFreeIn_LsubstI1)
apply assumption+
apply (drule spec [THEN spec, THEN iffD2], rule exI [THEN exI],
       erule LBoundBy_LLamI1)
apply (safe elim!: LBoundBy_LTermEs list.free_elims LTag.free_elims)
apply (rule_tac P="%z. LFreeIn(<z, TLVar(y)>, Lsubst(xa, x, LVar(y)))"
        in app_right_Nil [THEN subst])
apply (rule_tac [2] LFreeIn_LsubstI2)
apply (drule_tac [4] spec [THEN iffD1], erule_tac [4] asm_rl)
apply (erule LFreeInE2)
apply (erule LOcc_typeD1)
apply (assumption | rule LFO_I LFreeIn_LTermIs)+

apply (rule LFreeInE)
apply assumption
apply hypsubst
apply (erule LFreeIn_LsubstE)
apply (assumption | rule LTerm.intros)+
apply (safe elim!: LFreeIn_LTermEs LFO_E LTag.free_elims)
apply (drule spec [THEN iffD2], assumption)
apply (drule spec [THEN iffD1], erule LFreeIn_LLamI)
apply blast
apply assumption
apply (safe elim!: LFreeIn_LTermEs list.free_elims LTag.free_elims)
apply (subgoal_tac "n: list(nat)")
prefer 2
apply (erule LFreeInE2, erule LOcc_typeD1, assumption)
apply (simp only: app_right_Nil)
apply (drule spec [THEN iffD2], assumption)
apply (drule spec [THEN spec, THEN iffD1], rule exI [THEN exI],
       erule LBoundBy_LLamI1)
apply (safe elim!: LBoundBy_LTermEs list.free_elims LTag.free_elims)

apply (frule LBoundByD1)
apply (erule LBindingE)
apply (frule_tac [2] LBoundByD1)
apply (erule_tac [2] LBindingE)
apply safe
apply (drule spec [THEN spec, THEN iffD2], rule exI [THEN exI],
       erule LBoundBy_LLamI2)
apply assumption
apply (safe elim!: LBoundBy_LTermEs list.free_elims LTag.free_elims)
apply (drule spec [THEN spec, THEN iffD1], erule exI [THEN exI])
apply (erule exE)+
apply (frule_tac M="xa" in LBoundByD1)
apply (erule LBindingE)
apply clarify
apply (rule exI)+
apply (rule LBoundBy_LsubstI1)
apply (assumption | rule LTerm.intros)+

apply (safe elim!: LBoundBy_LsubstE LBoundBy_LTermEs
        list.free_elims LTag.free_elims)
apply (drule spec [THEN spec, THEN iffD2], erule exI [THEN exI])
apply (erule exE)+
apply (frule_tac M="M" in LBoundByD1)
apply (erule LBindingE)
apply safe
apply (drule spec [THEN spec, THEN iffD1], rule exI [THEN exI],
       erule LBoundBy_LLamI2)
apply assumption
apply (safe elim!: LBoundBy_LTermEs list.free_elims LTag.free_elims)
apply (erule exI [THEN exI])

apply (rule LFreeInE)
apply assumption
apply hypsubst
apply (rule_tac [2] LFreeInE)
prefer 2 apply assumption
apply (case_tac "xa = x")
apply hypsubst
prefer 2
apply (drule spec [THEN iffD1], erule LFreeIn_LLamI)
apply assumption+
apply (safe elim!: LFreeIn_LTermEs list.free_elims LTag.free_elims)
apply (drule spec [THEN spec, THEN iffD1], rule exI [THEN exI],
       erule LBoundBy_LLamI1)
apply (safe elim!: LBoundBy_LTermEs list.free_elims LTag.free_elims)

apply (case_tac "xa = x")
apply hypsubst
prefer 2
apply (drule spec [THEN iffD2], erule LFreeIn_LLamI)
apply assumption+
apply (safe elim!: LFreeIn_LTermEs list.free_elims LTag.free_elims)
apply (drule spec [THEN spec, THEN iffD2], rule exI [THEN exI],
       erule LBoundBy_LLamI1)
apply (safe elim!: LBoundBy_LTermEs list.free_elims LTag.free_elims)

apply (frule LBoundByD1)
apply (erule LBindingE)
apply (frule_tac [2] LBoundByD1)
apply (erule_tac [2] LBindingE)
apply safe
apply (drule spec [THEN spec, THEN iffD1], rule exI [THEN exI],
       erule LBoundBy_LLamI2)
apply (drule_tac [3] spec [THEN spec, THEN iffD2],
       rule_tac [3] exI [THEN exI],
       erule_tac [3] LBoundBy_LLamI2)
apply (safe elim!: LBoundBy_LTermEs list.free_elims LTag.free_elims)
apply (assumption | rule exI)+
done

lemma LAlpha_LAppE:
  assumes major: "LAlpha(LApp(A, B), N)"
  and prem: "!! C D. [| N = LApp(C, D); LAlpha(A, C); LAlpha(B, D) |] ==> R"
  shows "R"
apply (insert major)
apply (unfold LAlpha_def)
apply (elim conjE)
apply (erule LSkeltonEq_LAppE)
apply (subgoal_tac "A: LTerm" "B: LTerm" "C: LTerm" "D: LTerm")
defer 1
apply (erule LSkeltonEqD1 LSkeltonEqD2)+
apply (rule prem)
apply assumption
apply (unfold LAlpha_def)
apply safe

prefer 8 apply (frule LBoundByD1, erule LBindingE)
prefer 8 apply (frule LBoundByD1, erule LBindingE)
prefer 8 apply (rule LFreeInE, assumption, hypsubst)
prefer 8 apply (rule LFreeInE, assumption, hypsubst)
prefer 8 apply (frule LBoundByD1, erule LBindingE)
prefer 8 apply (frule LBoundByD1, erule LBindingE)
prefer 8 apply (rule LFreeInE, assumption, hypsubst)
prefer 8 apply (rule LFreeInE, assumption, hypsubst)
apply safe

apply (drule_tac [8] spec [THEN spec, THEN iffD2],
       rule_tac [8] exI [THEN exI],
       erule_tac [8] LBoundBy_LAppI2)
apply (drule_tac [7] spec [THEN spec, THEN iffD1],
       rule_tac [7] exI [THEN exI],
       erule_tac [7] LBoundBy_LAppI2)
apply (drule_tac [6] spec [THEN iffD2],
       erule_tac [6] LFreeIn_LAppI2)
apply (drule_tac [5] spec [THEN iffD1],
       erule_tac [5] LFreeIn_LAppI2)
apply (drule_tac [4] spec [THEN spec, THEN iffD2],
       rule_tac [4] exI [THEN exI],
       erule_tac [4] LBoundBy_LAppI1)
apply (drule_tac [3] spec [THEN spec, THEN iffD1],
       rule_tac [3] exI [THEN exI],
       erule_tac [3] LBoundBy_LAppI1)
apply (drule_tac [2] spec [THEN iffD2],
       erule_tac [2] LFreeIn_LAppI1)
apply (drule_tac [1] spec [THEN iffD1],
       erule_tac [1] LFreeIn_LAppI1)
apply (safe elim!: LFreeIn_LTermEs LBoundBy_LTermEs
         list.free_elims LTag.free_elims)
apply (assumption | rule exI)+
done

lemmas LAlpha_LTermEs = LAlpha_LVarE LAlpha_LLamE LAlpha_LAppE


(** Rules for depth induction **)
lemmas LTerm_Occ_Term_cons = Occ_Term_cons [OF
  LTerm_Occ_ind_cond LTerm_Term_cons_inj_cond]

lemma depth_ind_LLam:
  "[| LOcc(LLam(x, M)) <= Occ_fbs_op(LTag, Z); x: LVariable; M: LTerm |]
     ==> LOcc(M) <= domain(Z) * LTag"
apply (rule_tac P="%x. x <= domain(Z) * LTag" in ssubst)
apply (erule_tac [2] b="0" in Occ_subtree_Occ_fbs_op_lemma)
apply (simp add: LTerm_cons_eqns_sym LTerm_Occ_Term_cons
        Occ_subtree_Occ_cons)
done

lemma depth_ind_LApp1:
  "[| LOcc(LApp(M, N)) <= Occ_fbs_op(LTag, Z); M: LTerm; N: LTerm |]
     ==> LOcc(M) <= domain(Z) * LTag"
apply (rule_tac P="%x. x <= domain(Z) * LTag" in ssubst)
apply (erule_tac [2] b="0" in Occ_subtree_Occ_fbs_op_lemma)
apply (simp add: LTerm_cons_eqns_sym LTerm_Occ_Term_cons
        Occ_subtree_Occ_cons)
done

lemma depth_ind_LApp2:
  "[| LOcc(LApp(M, N)) <= Occ_fbs_op(LTag, Z); M: LTerm; N: LTerm |]
     ==> LOcc(N) <= domain(Z) * LTag"
apply (rule_tac P="%x. x <= domain(Z) * LTag" in ssubst)
apply (erule_tac [2] b="1" in Occ_subtree_Occ_fbs_op_lemma)
apply (simp add: LTerm_cons_eqns_sym LTerm_Occ_Term_cons
        Occ_subtree_Occ_cons)
done

lemma depth_ind_LSkeltonEq:
  "[| LSkeltonEq(M, N); LOcc(M) <= domain(Z) * LTag |] ==>
      LOcc(N) <= domain(Z) * LTag"
apply (unfold LSkeltonEq_def)
apply safe
apply (rule LOcc_domain [THEN subsetD, THEN SigmaE])
prefer 2 apply assumption
apply safe
apply (erule LTag.cases)
apply safe
prefer 3 apply (drule spec [THEN iffD2], assumption)
prefer 3 apply (drule spec [THEN iffD2], erule exI)
apply (erule exE)
prefer 3 apply (drule spec [THEN iffD2], erule exI)
apply (erule exE)
apply (drule subsetD, assumption, erule SigmaD1)+
done

lemma LAlpha_LsubstI:
  assumes prem1: "LAlpha(M, M')"
  and prem2: "LAlpha(N, N')"
  and prem3: "LFreeForIn(N, x, M)"
  and prem4: "LFreeForIn(N', x, M')"
  shows "LAlpha(Lsubst(M, x, N), Lsubst(M', x, N'))"
apply (subgoal_tac "M: LTerm" "M': LTerm" "N: LTerm" "N': LTerm")
defer 1
apply (rule prem1 [THEN LAlphaD1, THEN LSkeltonEqD1]
            prem1 [THEN LAlphaD1, THEN LSkeltonEqD2]
            prem2 [THEN LAlphaD1, THEN LSkeltonEqD1]
            prem2 [THEN LAlphaD1, THEN LSkeltonEqD2])+
apply (insert prem3 prem4)
apply (rule LAlphaI)
apply (unfold LSkeltonEq_def)
apply (safe elim!: LOcc_LsubstE LFO_E2 intro!: Lsubst_type)
apply (drule_tac [2] prem1 [THEN LAlphaD2]
                     prem1 [THEN LAlpha_sym, THEN LAlphaD2])
apply (drule_tac [4] prem1 [THEN LAlphaD2]
                     prem1 [THEN LAlpha_sym, THEN LAlphaD2])
apply (drule_tac [6] prem1 [THEN LAlphaD2]
                     prem1 [THEN LAlpha_sym, THEN LAlphaD2])
apply (drule_tac [8] prem1 [THEN LAlphaD2]
                     prem1 [THEN LAlpha_sym, THEN LAlphaD2])
apply (drule_tac [10] prem1 [THEN LAlphaD2]
                      prem1 [THEN LAlpha_sym, THEN LAlphaD2])
apply (drule_tac [12] prem1 [THEN LAlphaD2]
                      prem1 [THEN LAlpha_sym, THEN LAlphaD2])
apply (frule_tac [1] prem1 [THEN LAlphaD1, THEN LSkeltonEq_TLVarD])
apply (frule_tac [2] prem2 [THEN LAlphaD1, THEN LSkeltonEq_TLVarD])
apply (frule_tac [3] prem1 [THEN LAlpha_sym, THEN LAlphaD1, THEN LSkeltonEq_TLVarD])
apply (frule_tac [4] prem2 [THEN LAlpha_sym, THEN LAlphaD1, THEN LSkeltonEq_TLVarD])
apply (frule_tac [5] prem1 [THEN LAlphaD1, THEN LSkeltonEq_TLLamD])
apply (frule_tac [6] prem2 [THEN LAlphaD1, THEN LSkeltonEq_TLLamD])
apply (frule_tac [7] prem1 [THEN LAlpha_sym, THEN LAlphaD1, THEN LSkeltonEq_TLLamD])
apply (frule_tac [8] prem2 [THEN LAlpha_sym, THEN LAlphaD1, THEN LSkeltonEq_TLLamD])
apply (frule_tac [9] prem1 [THEN LAlphaD1, THEN LSkeltonEq_TLAppD])
apply (frule_tac [10] prem2 [THEN LAlphaD1, THEN LSkeltonEq_TLAppD])
apply (frule_tac [11] prem1 [THEN LAlpha_sym, THEN LAlphaD1, THEN LSkeltonEq_TLAppD])
apply (frule_tac [12] prem2 [THEN LAlpha_sym, THEN LAlphaD1, THEN LSkeltonEq_TLAppD])
apply safe
apply (erule_tac [12] LFO_I [THEN LOcc_LsubstI2])
apply (rule_tac [11] LOcc_LsubstI1)
apply (erule_tac [10] LFO_I [THEN LOcc_LsubstI2])
apply (rule_tac [9] LOcc_LsubstI1)
apply (rule_tac [8] exI, erule_tac [8] LFO_I [THEN LOcc_LsubstI2])
apply (rule_tac [7] exI, rule_tac [7] LOcc_LsubstI1)
apply (rule_tac [6] exI, erule_tac [6] LFO_I [THEN LOcc_LsubstI2])
apply (rule_tac [5] exI, rule_tac [5] LOcc_LsubstI1)
apply (rule_tac [4] exI, erule_tac [4] LFO_I [THEN LOcc_LsubstI2])
apply (rule_tac [3] exI, rule_tac [3] LOcc_LsubstI1)
apply (rule_tac [2] exI, erule_tac [2] LFO_I [THEN LOcc_LsubstI2])
apply (rule_tac [1] exI, rule_tac [1] LOcc_LsubstI1)
defer 1 apply assumption+
defer 1 apply assumption+
defer 1 apply assumption+
defer 1 apply assumption+
defer 1 apply assumption+
defer 1 apply assumption+
defer 1
defer 1
defer 1
defer 1
apply (safe elim!: LFO_E LTag.free_elims)
apply (drule_tac [2] prem1 [THEN LAlphaD2])
apply (drule_tac [1] prem1 [THEN LAlpha_sym, THEN LAlphaD2])
apply (subgoal_tac [2] "TLVar(xa) = TLVar(x)")
prefer 3
apply (erule LFreeInE2)
apply (rule LOcc_in_Occ_range [THEN Occ_range_functionalD,
        THEN functionalD])
prefer 2 apply assumption
apply assumption+
apply (subgoal_tac "TLVar(xa) = TLVar(x)")
prefer 2
apply (erule LFreeInE2)
apply (rule LOcc_in_Occ_range [THEN Occ_range_functionalD,
        THEN functionalD])
prefer 2 apply assumption
apply assumption+
apply (erule notE, simp, erule LFO_I)+
apply (safe elim!: LFreeIn_LsubstE LBoundBy_LsubstE LFO_E2)
apply (drule_tac [8] prem2 [THEN LAlpha_sym, THEN LAlphaD3])
apply (drule_tac [7] prem1 [THEN LAlpha_sym, THEN LAlphaD3])
apply (drule_tac [6] prem2 [THEN LAlphaD3])
apply (drule_tac [5] prem1 [THEN LAlphaD3])
apply (blast intro: prem1 [THEN LAlphaD2] prem2 [THEN LAlphaD2]
        prem1 [THEN LAlpha_sym, THEN LAlphaD2]
        prem2 [THEN LAlpha_sym, THEN LAlphaD2]
        LFO_I LFreeIn_LsubstI2 LFreeIn_LsubstI1
        LBoundBy_LsubstI2 LBoundBy_LsubstI1)+
done

end
