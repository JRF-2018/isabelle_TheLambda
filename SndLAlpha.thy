(*
    File:        SndLAlpha.thy
    Time-stamp:  <2016-01-06T16:55:28Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory SndLAlpha imports LAlpha begin

consts
  LAlpha2 :: i
  
inductive
  domains "LAlpha2" <= "LTerm * LTerm"
  intros
    LVarI: "x: LVariable ==> <LVar(x), LVar(x)>: LAlpha2"
    LAppI: "[| <A, C>: LAlpha2; <B, D>: LAlpha2 |]
                ==> <LApp(A, B), LApp(C, D)>: LAlpha2"
    LLamI: "[| x: LVariable; y: LVariable; <M, N>: LAlpha2; 
               y ~: LFV(N) - {x}; LFreeForIn(LVar(y), x, N) |]
             ==> <LLam(x, M), LLam(y, Lsubst(N, x, LVar(y)))>: LAlpha2"

    transI: "[| <A, B>: LAlpha2; <B, C>: LAlpha2 |] ==> <A, C>: LAlpha2"

  type_intros LTerm.intros SigmaI Lsubst_type
  type_elims SigmaE2

lemma LAlpha2_induct:
  assumes major: "<M, N>: LAlpha2"
  and
   "!!x. x : LVariable ==> P(LVar(x), LVar(x))"
  and
   "!!A B C D. [| <A, C> : LAlpha2; P(A, C); <B, D> : LAlpha2; P(B, D) |]
       ==> P(LApp(A, B), LApp(C, D))"
  and
   "!!M N x y.
       [| x : LVariable; y : LVariable; <M, N> : LAlpha2; P(M, N);
          y ~: LFV(N) - {x}; LFreeForIn(LVar(y), x, N) |] ==>
       P(LLam(x, M), LLam(y, Lsubst(N, x, LVar(y))))"
  and
   "!!A B C.
       [| <A, B> : LAlpha2; P(A, B); <B, C> : LAlpha2; P(B, C) |] ==>
          P(A, C)"
  shows "P(M, N)"
apply (rule_tac P="%x. P(x, N)" and b1="N" in fst_conv [THEN subst])
apply (rule_tac P="%x. P(fst(<M,N>),x)" and a1="M" in snd_conv [THEN subst])
apply (rule major [THEN LAlpha2.induct])
apply simp_all
apply (blast intro: assms)+
done

lemma LAlpha2_refl:
  "M: LTerm ==> <M, M>: LAlpha2"
apply (erule LTerm.induct)
apply (erule LAlpha2.LVarI)
apply (erule_tac [2] LAlpha2.LAppI)
prefer 2 apply assumption
apply (rule_tac P="%z. <LLam(x, M), z>: LAlpha2" in ssubst)
apply (rule_tac [2] y="x" in LAlpha2.LLamI)
apply (erule_tac [2] asm_rl)+
prefer 2 apply simp
apply (erule_tac [2] LFreeForIn_left_LVarI)
prefer 2 apply assumption
apply (simp only: Lsubst_self)
done

lemma LAlpha2_sym:
  "<M, N>: LAlpha2 ==> <N, M>: LAlpha2"
apply (erule LAlpha2_induct)
apply (erule LAlpha2.LVarI)
apply (erule LAlpha2.LAppI)
apply assumption
apply (erule_tac [2] LAlpha2.transI)
prefer 2 apply assumption
apply (frule LAlpha2.dom_subset [THEN subsetD])
apply (erule SigmaE2)
apply simp
apply (erule disjE)
prefer 2
apply hypsubst
apply (simp add: Lsubst_self)
apply (rule_tac P="%z. <LLam(x, N), z>: LAlpha2" in subst)
apply (rule_tac [2] N="M" and y="x" in LAlpha2.LLamI)
apply (simp add: Lsubst_self)
prefer 4 apply blast
apply (assumption | rule LFreeForIn_left_LVarI)+
apply (rule_tac B="LLam(x, Lsubst(Lsubst(N,x, LVar(y)), y, LVar(x)))"
        in LAlpha2.transI)
prefer 2
apply (simp add: Lsubst_self Lsubst_lemma2)
apply (rule_tac P="%z. <LLam(x, N), z>: LAlpha2" in subst)
apply (rule_tac [2] N="M" and y="x" in LAlpha2.LLamI)
apply (simp add: Lsubst_self)
prefer 4 apply blast
apply (assumption | rule LFreeForIn_left_LVarI)+
apply (rule LAlpha2.LLamI)
apply (assumption | rule LAlpha2_refl Lsubst_type LTerm.intros)+
prefer 2
apply (assumption | rule LFreeForIn_left_LVarI LFreeForIn_name_change)+
apply (safe elim!: LFV_E LFreeIn_LsubstE LTag.free_elims
         LFreeIn_LTermEs)
done

lemma LAlpha2_LFV_lemma:
  assumes major: "<M, N>: LAlpha2"
  and prem: "x: LFV(M)"
  shows "x: LFV(N)"
apply (rule prem [THEN rev_mp])
apply (rule major [THEN LAlpha2_induct])
apply (subgoal_tac [2] "A: LTerm" "B: LTerm" "C: LTerm" "D: LTerm")
apply (erule_tac [3] LAlpha2.dom_subset [THEN subsetD, THEN SigmaD1]
         LAlpha2.dom_subset [THEN subsetD, THEN SigmaD2])+
apply simp_all
apply blast
apply (frule LAlpha2.dom_subset [THEN subsetD])
apply safe
prefer 2 apply (simp add: Lsubst_self)
apply (erule LFV_E)+
apply (rule LFV_I)
apply (erule LFreeIn_LsubstI1)
apply assumption
apply blast
done

lemma LAlpha2_LAlpha:
  "<M, N>: LAlpha2 ==> LAlpha(M, N)"
apply (erule LAlpha2_induct)
apply (rule_tac [4] LAlpha_trans)
apply (erule_tac [4] asm_rl)+
apply (assumption | rule LAlpha_LVarI LAlpha_LAppI)+
apply (case_tac "y = x")
prefer 2
apply simp
apply safe
apply (erule_tac [3] swap, rule_tac [3] LAlpha_LLamI1)
apply (erule_tac [2] swap, rule_tac [2] LAlpha_LLamI1)
prefer 2 apply (simp add: Lsubst_self LFreeForInD3)
prefer 3 apply (simp add: Lsubst_self LFreeForInD3)
apply (erule_tac [2] asm_rl)+
apply (rule LAlpha_LLamI2)
apply (simp add: Lsubst_lemma2 Lsubst_self LFreeForInD3)
apply (rule LFreeForIn_name_change)
apply (rule_tac [4] LFV_Lsubst_notI)
apply (assumption | rule LFreeForIn_left_LVarI
       | erule LFreeForInD3)+
done

lemmas LTerm_def_Terms_depth_induct = def_Terms_depth_induct [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LOccinv_def]

lemma LAlpha_LAlpha2:
  assumes infv: "Infinite(LVariable)"
  and prem: "LAlpha(M, N)"
  shows "<M, N>: LAlpha2"
apply (insert prem [THEN LAlphaD1, THEN LSkeltonEqD1])
apply (rule prem [THEN rev_mp])
apply (rule_tac x="N" in spec)
apply (erule_tac M="M" in LTerm_def_Terms_depth_induct)
apply (erule_tac LTerm.cases)
apply (safe elim!: LAlpha_LTermEs)
apply (frule_tac [3] depth_ind_LApp1)
apply (frule_tac [5] depth_ind_LApp2)
apply (rule_tac [7] LAlpha2.LAppI)
apply (erule_tac [8] bspec [THEN mp, THEN spec, THEN mp],
       erule_tac [8] asm_rl)
apply (erule_tac [7] bspec [THEN mp, THEN spec, THEN mp],
       erule_tac [7] asm_rl)
apply (erule_tac [3] asm_rl)+
apply (assumption | rule LAlpha2.LVarI)+
apply (erule infv [THEN LAlpha_LLamE])
prefer 2 apply hypsubst
prefer 2 apply hypsubst

apply (frule_tac LAlphaD1 [THEN LSkeltonEqD2])
apply (rule_tac P="%z. <LLam(x, Ma), z>: LAlpha2" in ssubst)
apply (rule_tac [2] y="x" and N="N'" in LAlpha2.LLamI)
apply (simp add: Lsubst_self)
prefer 4 apply simp
apply (frule_tac [3] depth_ind_LLam)
apply (erule_tac [5] bspec [THEN mp, THEN spec, THEN mp],
       erule_tac [5] asm_rl)
apply (assumption | rule LFreeForIn_left_LVarI)+
apply (subgoal_tac "M': LTerm" "N': LTerm" "y: LVariable"
                   "LOcc(Ma) <= domain(Z) * LTag"
                   "LOcc(M') <= domain(Z) * LTag"
                   "LOcc(N') <= domain(Z) * LTag")
apply (erule_tac [7] LAlphaD1 [THEN LSkeltonEqD2])
apply (erule_tac [6] LAlphaD1 [THEN LSkeltonEqD1])
apply (erule_tac [5] LFreeForInE)
apply (erule_tac [5] LTerm_typeEs)
apply (erule_tac [4] depth_ind_LLam)
apply (rule_tac [3] depth_ind_LSkeltonEq)
apply (erule_tac [3] LAlphaD1)
apply (rule_tac [2] depth_ind_LSkeltonEq)
apply (rule_tac [2] LSkeltonEq_trans)
apply (erule_tac [3] LAlphaD1 [THEN LSkeltonEq_sym])
apply (rule_tac [2] LSkeltonEq_Lsubst_LVar)
apply (erule_tac [2] asm_rl)+
apply (rule_tac P="%z. <LLam(x, Ma), z>: LAlpha2" in ssubst)
apply (rule_tac [2] LAlpha2.transI)
apply (rule_tac [3] y="y" and N="N'" in LAlpha2.LLamI)
apply (rule_tac [2] y="y" and N="M'" in LAlpha2.LLamI)
apply (rule_tac [9] LAlpha2_sym)
prefer 2
prefer 3
prefer 6
prefer 7
prefer 8
apply assumption+
apply (erule_tac [4] bspec [THEN mp, THEN spec, THEN mp],
       erule_tac [4] asm_rl)
apply (erule_tac [2] bspec [THEN mp, THEN spec, THEN mp],
       erule_tac [2] asm_rl)
apply (simp only: Lsubst_self)
prefer 3 apply blast
prefer 5 apply blast
apply (assumption | rule LFreeForIn_left_LVarI)+
done

lemma LAlpha2_iff_LAlpha:
  assumes prem: "Infinite(LVariable)"
  shows "<M,N>:LAlpha2 <-> LAlpha(M,N)"
apply (rule iffI)
apply (erule LAlpha2_LAlpha)
apply (erule prem [THEN LAlpha_LAlpha2])
done

lemmas LAlpha2_LSkeltonEq = LAlpha2_LAlpha [THEN LAlphaD1, rule_format]

lemma LAlpha2_LVarE_lemma:
  "<M, N>: LAlpha2 ==> M = LVar(x) --> N = LVar(x)"
apply (erule LAlpha2_induct)
apply (safe elim!: LTerm.free_elims)
done

lemma LAlpha2_LVarD:
  "<LVar(x), N>: LAlpha2 ==>  N = LVar(x)"
apply (erule LAlpha2_LVarE_lemma [THEN mp])
apply (rule refl)
done

lemma LAlpha2_LAppE_lemma:
  "<M, N>: LAlpha2 ==>
    (ALL A B. (M = LApp(A, B) -->
        (EX C D. N = LApp(C, D) & <A, C>: LAlpha2 & <B, D>: LAlpha2)))"
apply (erule LAlpha2_induct)
apply (blast elim!: LTerm.free_elims)
apply (blast elim!: LTerm.free_elims)
apply (blast elim!: LTerm.free_elims)
apply (safe elim!: LTerm.free_elims)
apply (drule spec [THEN spec, THEN mp], rule refl)
apply (elim exE conjE)
apply (drule spec [THEN spec, THEN mp], assumption)
apply (safe elim!: LTerm.free_elims)
apply (blast intro: LAlpha2.transI)
done

lemma LAlpha2_LAppE:
  assumes major: "<LApp(A, B), N>: LAlpha2"
  and prem1:
     "!! C D. [| N = LApp(C, D); <A, C>: LAlpha2; <B, D>: LAlpha2 |] ==> R"
  shows "R"
apply (insert major [THEN LAlpha2_LAppE_lemma])
apply (drule spec [THEN spec, THEN mp])
apply (rule refl)
apply (elim exE conjE)
apply (rule prem1)
apply assumption+
done

lemma Lsubst_eq_LVar_lemma:
  assumes major: "Lsubst(N, x, LVar(y)) = LVar(z)"
  and sub: "N: LTerm"
  and prem1: "y: LVariable"
  and prem2: "z: LVariable"
  shows "N = LVar(x) & y = z  | N = LVar(x) & y = z
                         | N = LVar(z) & x ~= z"
apply (insert assms)
apply (rule sub [THEN LTerm.cases])
apply (case_tac [2] "x = xa")
apply (case_tac [1] "x = xa")
apply simp_all
done

lemma Lsubst_eq_LLam_lemma:
  assumes major: "Lsubst(N, x, LVar(y)) = LLam(x, M)"
  and sub: "N: LTerm"
  and prem1: "M: LTerm"
  and prem2: "y: LVariable"
  shows "N = LLam(x, M)"
apply (insert assms)
apply (rule sub [THEN LTerm.cases])
apply (case_tac [2] "x = xa")
apply (case_tac "x = xa")
apply simp_all
done

lemma LAlpha2_LLam_LVar_lemma1:
  "[| <M, N>: LAlpha2; LVariable = {x, y}; y ~= x |]
       ==> M = LLam(y, LVar(x)) --> N = LLam(y, LVar(x))"
apply (erule LAlpha2_induct)
prefer 3 apply simp
prefer 3
prefer 3
prefer 4 apply (blast elim!: LTerm.free_elims)
prefer 1 apply (blast elim!: LTerm.free_elims)
prefer 1 apply (blast elim!: LTerm.free_elims)
apply (frule LAlpha2.dom_subset [THEN subsetD])
apply (erule SigmaE2)
apply (erule disjE)
prefer 2 apply hypsubst
apply (rule impI)
apply (erule conjE)
apply hypsubst
apply (rule conjI)
apply (rule refl)
apply (drule LAlpha2_LVarD)
apply (simp only: Lsubst_self)

apply (rule impI)
apply (erule conjE)
apply hypsubst
apply (drule LAlpha2_LVarD)
apply hypsubst
apply (erule LFreeForIn_LVarE)
apply simp
apply (subgoal_tac "ya : {x, y}")
apply blast
apply (erule subst)
apply assumption
done

lemma LAlpha2_LLam_LLam_LVar_lemma1:
  assumes major: "<M, N>: LAlpha2"
  and prem1: "LVariable = {x, y}"
  and prem2: "y ~= x"
  shows "M = LLam(x, LLam(y, LVar(x)))
          --> N = LLam(x, LLam(y, LVar(x)))"
apply (insert prem1 prem2)
apply (rule major [THEN LAlpha2_induct])
prefer 3 apply simp
defer 1
apply (blast elim!: LTerm.free_elims)
apply (blast elim!: LTerm.free_elims)
apply (blast elim!: LTerm.free_elims)
apply (frule LAlpha2.dom_subset [THEN subsetD])
apply (erule SigmaE2)
apply (erule disjE)
prefer 2 apply hypsubst
apply (rule impI)
apply (erule conjE)
apply hypsubst
prefer 2
apply (rule impI)
apply (erule conjE)
apply hypsubst
apply (frule LAlpha2_LLam_LVar_lemma1 [THEN mp])
apply (assumption | rule refl)+
apply hypsubst
apply (erule LFreeForIn_LLamE)
apply blast
apply (erule LFreeForIn_LVarE)
apply simp
apply (subgoal_tac "ya: {x, y}")
apply blast
apply (erule subst)
apply assumption
apply simp
apply (simp add: Lsubst_self)
apply (frule LAlpha2_LLam_LVar_lemma1 [THEN mp])
apply (assumption | rule refl)+
done

lemma LAlpha2_LLam_LLam_LVar_lemma:
  "[| LVariable = {x, y}; y ~= x |] ==>
      <LLam(x, LLam(y, LVar(x))), LLam(y, LLam(x, LVar(y)))> ~: LAlpha2"
apply (rule notI)
apply (drule LAlpha2_LLam_LLam_LVar_lemma1)
apply (drule_tac [3] mp)
apply (assumption | rule refl)+
apply (safe elim!: LTerm.free_elims)
done

lemma LAlpha_LLam_LLam_LVar_lemma:
  "[| LVariable = {x, y}; y ~= x |] ==>
      LAlpha(LLam(x, LLam(y, LVar(x))), LLam(y, LLam(x, LVar(y))))"
apply (subgoal_tac "x: LVariable" "y: LVariable")
defer 1
apply (erule ssubst)
apply blast
apply (erule ssubst)
apply blast
apply (rule LAlphaI)
apply (assumption | rule LSkeltonEq_LTermIs)+
apply (safe elim!: LFreeIn_LTermEs LBoundBy_LTermEs LTag.free_elims)
apply (assumption | rule exI LBoundBy_LTermIs LFreeIn_LTermIs)+
done

end
