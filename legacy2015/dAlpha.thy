(*
    File:        dAlpha.thy
    Time-stamp:  <2016-01-12T14:47:32Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory dAlpha imports dLambda begin

definition dSkeltonEq :: "[i, i] => o" where
"dSkeltonEq(M, N) == M: dTerm & N: dTerm &
   (ALL l. (EX x. <l, TdVar(x)>: dOcc(M))
                    <-> (EX x. <l, TdVar(x)>: dOcc(N))) &
   (ALL l. (EX n. <l, TdBound(n)>: dOcc(M))
                    <-> (EX n. <l, TdBound(n)>: dOcc(N))) &
   (ALL l. <l, TdLam>: dOcc(M) <-> <l, TdLam>: dOcc(N)) &
   (ALL l. <l, TdApp>: dOcc(M) <-> <l, TdApp>: dOcc(N))"

definition dAlpha :: "[i, i]=>o" where
"dAlpha(M, N) == dSkeltonEq(M, N) &
   (ALL l x. <l, TdVar(x)>: dOcc(M) <-> <l, TdVar(x)>: dOcc(N)) &
   (ALL l m. (EX T U. dBoundBy(<l, T>, <m, U>, M))
                     <-> (EX T U. dBoundBy(<l, T>, <m, U>, N)))"


(** dSkeltonEq **)
lemma dSkeltonEqD1:
  "dSkeltonEq(M, N) ==> M: dTerm"
apply (unfold dSkeltonEq_def)
apply (erule conjunct1)
done

lemma dSkeltonEqD2:
  "dSkeltonEq(M, N) ==> N: dTerm"
apply (unfold dSkeltonEq_def)
apply (erule conjunct2 [THEN conjunct1])
done

lemma dSkeltonEq_TdVarD:
  "[| dSkeltonEq(M, N); <l, TdVar(x)>: dOcc(M) |]
      ==> EX x. <l, TdVar(x)>: dOcc(N)"
apply (unfold dSkeltonEq_def)
apply blast
done

lemma dSkeltonEq_TdBoundD:
  "[| dSkeltonEq(M, N); <l, TdBound(n)>: dOcc(M) |]
      ==> EX n. <l, TdBound(n)>: dOcc(N)"
apply (unfold dSkeltonEq_def)
apply blast
done

lemma dSkeltonEq_TdLamD:
  "[| dSkeltonEq(M, N); <l, TdLam>: dOcc(M) |]
      ==> <l, TdLam>: dOcc(N)"
apply (unfold dSkeltonEq_def)
apply blast
done

lemma dSkeltonEq_TdAppD:
  "[| dSkeltonEq(M, N); <l, TdApp>: dOcc(M) |]
      ==> <l, TdApp>: dOcc(N)"
apply (unfold dSkeltonEq_def)
apply blast
done

lemma dSkeltonEq_refl:
  "M: dTerm ==> dSkeltonEq(M, M)"
apply (unfold dSkeltonEq_def)
apply blast
done

lemma dSkeltonEq_sym:
  "dSkeltonEq(M, N) ==> dSkeltonEq(N, M)"
apply (unfold dSkeltonEq_def)
apply blast
done

lemma dSkeltonEq_trans:
  "[| dSkeltonEq(M, N); dSkeltonEq(N, L) |] ==> dSkeltonEq(M, L)"
apply (unfold dSkeltonEq_def)
apply (erule conjE)+
apply ((erule spec [THEN iff_trans], erule spec)
       | (assumption | rule conjI allI))+
done

lemma dSkeltonEq_dVarI:
  "[| x: LVariable; y: LVariable |] ==> dSkeltonEq(dVar(x), dVar(y))"
apply (unfold dSkeltonEq_def)
apply (assumption | rule dTerm.intros conjI)+
apply (blast elim!: dTag.free_elims dOcc_dTermEs
         intro: dOcc_dTermIs)+
done

lemma dSkeltonEq_dBoundI:
  "[| n: nat; m: nat |] ==> dSkeltonEq(dBound(n), dBound(m))"
apply (unfold dSkeltonEq_def)
apply (assumption | rule dTerm.intros conjI)+
apply (blast elim!: dTag.free_elims dOcc_dTermEs
         intro: dOcc_dTermIs)+
done

lemma dSkeltonEq_dLamI:
  "dSkeltonEq(M, N) ==> dSkeltonEq(dLam(M), dLam(N))"
apply (unfold dSkeltonEq_def)
apply (erule conjE)+
apply (assumption | rule dTerm.intros conjI)
apply (safe elim!: dTag.free_elims dOcc_dTermEs)
apply (blast intro: dOcc_dTermIs)+
done

lemma dSkeltonEq_dAppI:
  "[| dSkeltonEq(A, C); dSkeltonEq(B, D)|]
      ==> dSkeltonEq(dApp(A, B), dApp(C, D))"
apply (unfold dSkeltonEq_def)
apply (erule conjE)+
apply (assumption | rule dTerm.intros conjI)
apply (safe elim!: dTag.free_elims dOcc_dTermEs)
apply (blast intro!: dOcc_dTermIs)+
done

lemmas dSkeltonEq_LTermIs = dSkeltonEq_dVarI dSkeltonEq_dBoundI
                          dSkeltonEq_dLamI dSkeltonEq_dAppI

lemma dSkeltonEq_dVarE:
  assumes major: "dSkeltonEq(dVar(x), N)"
  and prem:
     "!! y B. [| N = dVar(y); x: LVariable; y: LVariable |] ==> R"
  shows "R"
apply (insert major)
apply (unfold dSkeltonEq_def)
apply (elim dTerm_typeEs conjE)
apply (subgoal_tac "EX y. <[], TdVar(y)>: dOcc(N)"
                   "EX y: LVariable.  N = dVar(y)")
prefer 3
apply (erule spec [THEN iffD1])
apply (assumption | rule exI dOcc_dTermIs)+
prefer 2
apply (erule exE)
apply (erule_tac a="N" in dTerm.cases)
prefer 4
apply hypsubst
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
prefer 3
apply hypsubst
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
prefer 2
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
apply (assumption | rule bexI)+
apply (erule bexE)
apply (rule prem)
apply assumption+
done

lemma dSkeltonEq_dBoundE:
  assumes major: "dSkeltonEq(dBound(n), N)"
  and prem: "!! m B. [| N = dBound(m); n: nat; m: nat |] ==> R"
  shows "R"
apply (insert major)
apply (unfold dSkeltonEq_def)
apply (elim dTerm_typeEs conjE)
apply (subgoal_tac "EX m. <[], TdBound(m)>: dOcc(N)"
                   "EX m: nat.  N = dBound(m)")
prefer 3
apply (erule spec [THEN iffD1])
apply (assumption | rule exI dOcc_dTermIs)+
prefer 2
apply (erule exE)
apply (erule_tac a="N" in dTerm.cases)
prefer 4
apply hypsubst
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
prefer 3
apply hypsubst
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
prefer 1
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
apply (assumption | rule bexI)+
apply (erule bexE)
apply (rule prem)
apply assumption+
done

lemma dSkeltonEq_dLamE:
  assumes major: "dSkeltonEq(dLam(A), N)"
  and prem: "!! y B. [| N = dLam(B); dSkeltonEq(A, B) |] ==> R"
  shows "R"
apply (insert major)
apply (unfold dSkeltonEq_def)
apply (elim dTerm_typeEs conjE)
apply (subgoal_tac "<[], TdLam>: dOcc(N)"
                   "EX B: dTerm. N = dLam(B)")
prefer 3
apply (erule spec [THEN iffD1])
apply (assumption | rule exI dOcc_dTermIs)+
prefer 2
apply (erule_tac a="N" in dTerm.cases)
prefer 4
apply hypsubst
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
prefer 3
apply hypsubst
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
prefer 2
apply hypsubst
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
apply hypsubst
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
apply (elim bexE)
apply hypsubst
apply (rule prem)
apply assumption
apply (unfold dSkeltonEq_def)
apply (intro conjI)
apply assumption+

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

apply (intro allI iffI)
apply (drule spec [THEN iffD1], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (drule spec [THEN iffD2], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

apply (intro allI iffI)
apply (drule spec [THEN iffD1], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (drule spec [THEN iffD2], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
done

lemma dSkeltonEq_dAppE:
  assumes major: "dSkeltonEq(dApp(A, B), N)"
  and prem:
   "!! C D. [| N = dApp(C, D); dSkeltonEq(A, C); dSkeltonEq(B, D) |]
            ==> R"
  shows "R"
apply (insert major)
apply (unfold dSkeltonEq_def)
apply (elim dTerm_typeEs conjE)
apply (subgoal_tac "<[], TdApp>: dOcc(N)"
                   "EX C: dTerm.  EX D: dTerm. N = dApp(C, D)")
prefer 3
apply (erule spec [THEN iffD1])
apply (assumption | rule dOcc_dTermIs)+
prefer 2
apply (erule_tac a="N" in dTerm.cases)
apply hypsubst
apply (blast elim!: dTag.free_elims dOcc_dTermEs)
apply (blast elim!: dTag.free_elims dOcc_dTermEs)
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)
apply (blast elim!: dTag.free_elims list.free_elims dOcc_dTermEs)

apply (elim bexE)
apply (rule prem)
apply assumption
apply (unfold dSkeltonEq_def)

apply hypsubst
apply (intro conjI)
apply assumption+

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

apply (intro allI iffI)
apply (drule spec [THEN iffD1], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (drule spec [THEN iffD2], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

apply (intro allI iffI)
apply (drule spec [THEN iffD1], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (drule spec [THEN iffD2], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

apply hypsubst
apply (intro conjI)
apply assumption+

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

apply (intro allI iffI)
apply (erule exE)
apply (drule spec [THEN iffD1], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (erule exE)
apply (drule spec [THEN iffD2], rule exI, erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

apply (intro allI iffI)
apply (drule spec [THEN iffD1], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (drule spec [THEN iffD2], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

apply (intro allI iffI)
apply (drule spec [THEN iffD1], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)
apply (drule spec [THEN iffD2], erule dOcc_dTermIs)
apply (blast elim!: list.free_elims dTag.free_elims dOcc_dTermEs)

done

lemmas dSkeltonEq_dTermEs = dSkeltonEq_dVarE dSkeltonEq_dBoundE
                            dSkeltonEq_dLamE dSkeltonEq_dAppE

lemma dSkeltonEq_skelton:
  assumes major: "dSkeltonEq(M, N)"
  and prem: "<l, T>: dOcc(M)"
  shows "EX U. <l, U>: dOcc(N)"
apply (insert dOcc_typeD2 [OF prem major [THEN dSkeltonEqD1]] prem)
apply (erule dTag.cases)
apply hypsubst
apply (drule major [THEN dSkeltonEq_TdVarD])
apply (erule exE)
apply (erule exI)
apply hypsubst
apply (drule major [THEN dSkeltonEq_TdBoundD])
apply (erule exE)
apply (erule exI)
apply hypsubst
apply (drule major [THEN dSkeltonEq_TdLamD])
apply (erule exI)
apply hypsubst
apply (drule major [THEN dSkeltonEq_TdAppD])
apply (erule exI)
done

lemmas dTerm_Occ_ind_cond_Occ_not_empty_lemma
  = Occ_ind_cond_Occ_not_empty_lemma [OF dTerm_Occ_ind_cond]

lemma dSkeltonEq_dLamDeg_lemma:
  assumes major: "dSkeltonEq(M, N)"
  and prem1: "<l, T>: dOcc(M)"
  and prem2: "<l @ x, U>: dOcc(M)"
  shows "dLamDeg(x, dsubterm(M, l)) = dLamDeg(x, dsubterm(N, l))"
apply (rule prem2 [THEN rev_mp])
apply (rule prem1 [THEN rev_mp])
apply (rule major [THEN rev_mp])
apply (rule_tac x="N" in spec)
apply (rule_tac x="T" in spec)
apply (rule_tac x="l" and A="list(nat)" in bspec)
apply (rule_tac x="x" and A="list(nat)" in bspec)
prefer 3
prefer 3
apply (rule dOcc_typeD1 [OF prem2 major [THEN dSkeltonEqD1], 
        THEN app_typeD])
apply (rule dOcc_typeD1 [OF prem1 major [THEN dSkeltonEqD1]])+
apply (rule major [THEN dSkeltonEqD1, THEN dTerm.induct])
apply (safe elim!: dSkeltonEq_dTermEs ConsE dOcc_dTermEs
         dTag.free_elims)
apply (simp_all add: dTerm.intros dSkeltonEqD1 dSkeltonEqD2)
apply (safe elim!: list.free_elims ConsE)

apply (frule dSkeltonEqD1 [THEN dTerm_Occ_ind_cond_Occ_not_empty_lemma])
apply (erule bexE)
apply (drule_tac x6="l" and x5="[]" and x3="B" in bspec [THEN bspec, THEN spec, THEN spec,
       THEN mp, THEN mp, THEN mp])
apply (assumption | rule list.intros)+
apply simp
apply (simp add: dSkeltonEqD1 dSkeltonEqD2)

apply (frule dSkeltonEqD1 [THEN dTerm_Occ_ind_cond_Occ_not_empty_lemma])
apply (erule bexE)
apply (drule_tac x6="l" and x5="[]" and x3="C" in bspec [THEN bspec, THEN spec, THEN spec,
       THEN mp, THEN mp, THEN mp], erule_tac [4] asm_rl)
apply (assumption | rule list.intros)+
apply simp
apply (simp add: dSkeltonEqD1 dSkeltonEqD2)

apply (frule_tac M="N" in dSkeltonEqD1 [THEN dTerm_Occ_ind_cond_Occ_not_empty_lemma])
apply (erule bexE)
apply (drule_tac x6="l" and x5="[]" and x3="D" in bspec [THEN bspec, THEN spec, THEN spec,
       THEN mp, THEN mp, THEN mp], erule_tac [4] asm_rl)
apply (assumption | rule list.intros)+
apply simp
apply (simp add: dSkeltonEqD1 dSkeltonEqD2)
done


(** dAlpha **)
lemma dAlphaD1:
  "dAlpha(M, N) ==> dSkeltonEq(M, N)"
apply (unfold dAlpha_def)
apply (erule conjunct1)
done

lemma dAlphaD2:
  "[| dAlpha(M, N); <l, TdVar(x)>: dOcc(M) |] ==> <l, TdVar(x)>: dOcc(N)"
apply (unfold dAlpha_def)
apply blast
done

lemma dAlphaD3:
  "[| dAlpha(M, N); dBoundBy(<l, T>, <m, U>, M) |]
      ==> EX n. dBoundBy(<l, TdBound(n)>, <m, TdLam>, N)"
apply (unfold dAlpha_def)
apply (drule conjunct2 [THEN conjunct2])
apply (drule spec [THEN spec, THEN iffD1])
apply (erule exI [THEN exI])
apply (elim exE)
apply (rule_tac M="N" in dBoundByE)
apply assumption
apply safe
apply (erule exI)
done

lemma dAlpha_dBoundByD:
  assumes major: "dAlpha(M, N)"
  and prem: "dBoundBy(<l, T>, <m, U>, M)"
  shows "dBoundBy(<l, T>, <m, U>, N)"
apply (rule prem [THEN dBoundByE])
apply (insert dAlphaD3 [OF major prem])
apply (safe elim!: dBoundByE dest!: app_right_inj
            elim!: dTag.free_elims)
apply (erule dOcc_typeD1)
apply assumption
apply (frule major [THEN dAlphaD1, THEN dSkeltonEq_dLamDeg_lemma], assumption)
apply (simp only: succ_inject_iff)
apply (assumption | rule refl dBoundByI)+
done

lemma dAlphaI:
  assumes prem1: "dSkeltonEq(M, N)"
  and prem2: "!! l x. <l, TdVar(x)>: dOcc(M) <-> <l, TdVar(x)>: dOcc(N)"
  and prem3: "!! l m. (EX x. dBoundBy(<l, TdBound(x)>, <m, TdLam>, M))
               <-> (EX x. dBoundBy(<l, TdBound(x)>, <m, TdLam>, N))"
  shows "dAlpha(M, N)"
apply (unfold dAlpha_def)
apply (rule prem1 [THEN conjI])
apply (rule allI [THEN allI, THEN conjI])
apply (rule prem2)
apply safe
apply (rule_tac [2] dBoundByE, erule_tac [2] asm_rl)
apply (rule_tac [1] dBoundByE, erule_tac [1] asm_rl)
apply safe
apply (drule exI [THEN prem3 [THEN iffD1]])
apply (drule_tac [2] exI [THEN prem3 [THEN iffD2]])
apply blast+
done

lemma dAlpha_dPropI:
  assumes prem1: "M: dProp"
  and prem2: "N: dProp"
  and prem3:
     "!! l. <l, TdLam>: dOcc(M) <-> <l, TdLam>: dOcc(N)"
  and prem4:
     "!! l. <l, TdApp>: dOcc(M) <-> <l, TdApp>: dOcc(N)"
  and prem5:
     "!! l x. <l, TdVar(x)>: dOcc(M) <-> <l, TdVar(x)>: dOcc(N)"
  and prem6:
     "!! l m. (EX x. dBoundBy(<l, TdBound(x)>, <m, TdLam>, M))
              <-> (EX x. dBoundBy(<l, TdBound(x)>, <m, TdLam>, N))"
  shows "dAlpha(M, N)"
apply (rule dAlphaI)
apply (erule_tac [2] asm_rl | rule_tac [2] prem5 prem6)+
apply (unfold dSkeltonEq_def)
apply (assumption | rule conjI prem1 prem2 dPropD1)+
apply (rule_tac [2] conjI)
apply (rule_tac [3] conjI)
apply (rule_tac [4] allI)
apply (rule_tac [3] allI)
apply (rule_tac [2] allI)
apply (rule_tac [1] allI)
apply (erule_tac [3] asm_rl | rule_tac [3] prem3 prem4)+
apply safe
apply (drule prem5 [THEN iffD1], erule exI)
apply (drule prem5 [THEN iffD2], erule exI)
apply (drule prem1 [THEN dProp_dBoundBy_lemma1])
apply (drule_tac [2] prem2 [THEN dProp_dBoundBy_lemma1])
apply safe
apply (drule exI [THEN prem6 [THEN iffD1]])
apply (drule_tac [2] exI [THEN prem6 [THEN iffD2]])
apply (blast elim!: dBoundByE)+
done

lemma dAlpha_refl:
  "M: dTerm ==> dAlpha(M, M)"
apply (unfold dAlpha_def)
apply (blast intro: dSkeltonEq_refl)
done

lemma dAlpha_sym:
  "dAlpha(M, N) ==> dAlpha(N, M)"
apply (unfold dAlpha_def)
apply (blast intro: dSkeltonEq_sym)
done

lemma dAlpha_trans:
  "[| dAlpha(M, N); dAlpha(N, L) |] ==> dAlpha(M, L)"
apply (unfold dAlpha_def)
apply (blast intro: dSkeltonEq_trans)
done

lemmas dTerm_Occ_ind_cond_Occ_inj = Occ_ind_cond_Occ_inj [OF
  dTerm_Occ_ind_cond]

lemma dAlpha_imp_dProp_eq:
  assumes major: "dAlpha(M, N)"
  and prem1: "M: dProp"
  and prem2: "N: dProp"
  shows "M = N"
apply (insert prem1 [THEN dPropD1] prem2 [THEN dPropD1])
apply (rule dTerm_Occ_ind_cond_Occ_inj [THEN iffD1])
apply (assumption | rule equalityI)+
apply (rule_tac [2] subsetI)
apply (rule_tac [1] subsetI)
apply (rule_tac [2] dOcc_domain [THEN subsetD, THEN SigmaE],
       erule_tac [3] asm_rl)
apply (rule_tac [1] dOcc_domain [THEN subsetD, THEN SigmaE],
       erule_tac [2] asm_rl)
prefer 3
apply assumption+
apply (erule_tac [2] dTag.cases)
apply (erule_tac [1] dTag.cases)
prefer 6
apply hypsubst
apply (drule prem2 [THEN dProp_dBoundBy_lemma1])
apply (erule exE)
apply (drule major [THEN dAlpha_sym, THEN dAlpha_dBoundByD])
defer 1
defer 6
defer 6
prefer 2
apply hypsubst
apply (drule prem1 [THEN dProp_dBoundBy_lemma1])
apply (erule exE)
apply (drule major [THEN dAlpha_dBoundByD])
prefer 2
apply (safe elim!: dBoundByE dTag.free_elims)

apply (erule major [THEN dAlphaD2])
apply (erule major [THEN dAlphaD1, THEN dSkeltonEq_TdLamD])
apply (erule major [THEN dAlphaD1, THEN dSkeltonEq_TdAppD])
apply (erule major [THEN dAlpha_sym, THEN dAlphaD2])
apply (erule major [THEN dAlpha_sym, THEN dAlphaD1, THEN dSkeltonEq_TdLamD])
apply (erule major [THEN dAlpha_sym, THEN dAlphaD1, THEN dSkeltonEq_TdAppD])
done

lemma dAlpha_dProp_iff:
  assumes prem1: "M: dProp"
  and prem2: "N: dProp"
  shows "dAlpha(M, N) <-> M = N"
apply (rule iffI)
prefer 2
apply hypsubst
apply (rule prem2 [THEN dPropD1, THEN dAlpha_refl])
apply (erule dAlpha_imp_dProp_eq)
apply (rule prem1 prem2)+
done


(** Rules for depth induction **)
lemmas dTerm_Occ_Term_cons = Occ_Term_cons [OF
  dTerm_Occ_ind_cond dTerm_Term_cons_inj_cond]

lemma depth_ind_dLam:
  "[| dOcc(dLam(M)) <= Occ_fbs_op(dTag, Z); M: dTerm |]
     ==> dOcc(M) <= domain(Z) * dTag"
apply (rule_tac P="%x. x <= domain(Z) * dTag" in ssubst)
apply (erule_tac [2] b="0" in Occ_subtree_Occ_fbs_op_lemma)
apply (simp add: dTerm_Occ_Term_cons Occ_subtree_Occ_cons
        dTerm_cons_eqns_sym)
done

lemma depth_ind_dApp1:
  "[| dOcc(dApp(M, N)) <= Occ_fbs_op(dTag, Z); M: dTerm; N: dTerm |]
     ==> dOcc(M) <= domain(Z) * dTag"
apply (rule_tac P="%x. x <= domain(Z) * dTag" in ssubst)
apply (erule_tac [2] b="0" in Occ_subtree_Occ_fbs_op_lemma)
apply (simp add: dTerm_Occ_Term_cons Occ_subtree_Occ_cons
        dTerm_cons_eqns_sym)
done

lemma depth_ind_dApp2:
  "[| dOcc(dApp(M, N)) <= Occ_fbs_op(dTag, Z); M: dTerm; N: dTerm |]
     ==> dOcc(N) <= domain(Z) * dTag"
apply (rule_tac P="%x. x <= domain(Z) * dTag" in ssubst)
apply (erule_tac [2] b="1" in Occ_subtree_Occ_fbs_op_lemma)
apply (simp add: dTerm_Occ_Term_cons Occ_subtree_Occ_cons
        dTerm_cons_eqns_sym)
done

lemma depth_ind_dSubst_dVar_lemma:
  assumes major: "<l, T>: dOcc(dSubst(M, n, dVar(x)))"
  and prem1: "M: dTerm"
  and prem2: "x: LVariable"
  and prem3: "n: nat"
  shows "EX T. <l, T>: dOcc(M)"
apply (insert prem2)
apply (rule major [THEN rev_mp])
apply (rule prem3 [THEN [2] bspec])
apply (rule_tac x="l" in spec)
apply (rule prem1 [THEN dTerm.induct])
apply (rule_tac [2] ballI [THEN allI])
apply (case_tac [2] "xaa = n")
apply (case_tac [3] "xaa < n")
apply (simp_all del: all_simps ball_simps)
apply (safe elim!: dOcc_dTermEs)
apply (blast intro!: dOcc_dTermIs)+
done

lemma depth_ind_dSubst_dVar:
  assumes major: "dOcc(M) <= domain(Z) * dTag"
  and prem1: "M: dTerm"
  and prem2: "x: LVariable"
  and prem3: "n: nat"
  shows "dOcc(dSubst(M, n, dVar(x))) <= domain(Z) * dTag"
apply (rule subsetI)
apply (rule dOcc_domain [THEN subsetD, THEN SigmaE])
prefer 2 apply assumption
apply (assumption | rule dSubst_type prem1 prem2 prem3 dTerm.intros)+
apply hypsubst
apply (frule depth_ind_dSubst_dVar_lemma)
apply (erule_tac [4] exE)
apply (rule_tac [4] SigmaI)
apply (erule_tac [4] major [THEN subsetD, THEN SigmaD1])
apply (assumption | rule prem2 prem3 prem1)+
done

end
