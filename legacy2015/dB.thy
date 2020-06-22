(*
    File:        dB.thy
    Time-stamp:  <2016-01-06T12:59:06Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory dB imports dAlpha LAlpha begin

definition dB :: "i=>i" where
"dB(M) == LTerm_rec(%x. dVar(x), %x M r. dLam(dAbst(r, x, 0)),
                    %M N rm rn. dApp(rm, rn), M)"

definition LAlpha3 :: "[i,i] => o" where
"LAlpha3(M, N) == M: LTerm & N: LTerm & dB(M) = dB(N)"

definition dsubst :: "[i, i, i]=>i" where
"dsubst(M, x, N) == dSubst(dAbst(M, x, 0), 0, N)"

definition isSubst1 :: "[i,i,i,i]=>o" where
"isSubst1(A, x, B, C) == EX A'. LAlpha(A, A') & LFreeForIn(B, x, A') &
    LAlpha(Lsubst(A', x, B), C)"

definition isSubst2 :: "[i,i,i,i]=>o" where
"isSubst2(A, x, B, C) == A: LTerm & B: LTerm & C: LTerm & x: LVariable &
    dsubst(dB(A), x, dB(B)) = dB(C)"


lemma dB_eqns:
  "dB(LVar(x)) = dVar(x)"
  "dB(LLam(x, M)) = dLam(dAbst(dB(M), x, 0))"
  "dB(LApp(A, B)) = dApp(dB(A), dB(B))"
apply (unfold dB_def)
apply simp_all
done

lemma dB_type:
  "M: LTerm ==> dB(M): dProp"
apply (erule LTerm.induct)
apply (simp_all only: dB_eqns)
apply (case_tac [2] "x : dFV(dB(M))")
apply (erule_tac [2] dPropE)
apply (rule_tac [2] dProp_dLamI2)
prefer 3 apply (simp add: dDeg_dAbst_lemma2)
apply (frule_tac [3] dPropD1)
prefer 3 apply (simp add: dDeg_dAbst_lemma1)
apply (erule dProp_dLamI1)
apply (assumption | rule dProp_dTermIs dAbst_type nat_0I)+
done

lemma LFreeIn_imp_dFreeIn:
  assumes prem: "LFreeIn(<l, TLVar(x)>, M)"
  shows "<l, TdVar(x)>: dOcc(dB(M))"
apply (rule prem [THEN rev_mp])
apply (rule_tac x="l" in spec)
apply (rule prem [THEN LFreeInD1, THEN LTerm.induct])
apply (simp_all only: dB_eqns)
apply (safe elim!: LFreeIn_LTermEs LTag.free_elims
            intro!: dOcc_dTermIs)
apply (rule dOcc_dAbstI2)
apply (erule_tac [3] dB_type [THEN dPropD1])
apply (rule_tac [3] nat_0I)
prefer 2 apply (blast elim!: dTag.free_elims)
apply simp_all
done

lemma dFreeIn_imp_LFreeIn:
  assumes prem1: "<l, TdVar(x)>: dOcc(dB(M))"
  and prem2: "M: LTerm"
  shows "LFreeIn(<l, TLVar(x)>, M)"
apply (rule prem1 [THEN rev_mp])
apply (rule_tac x="l" in spec)
apply (rule prem2 [THEN LTerm.induct])
apply (simp_all only: dB_eqns)
apply (safe elim!: dOcc_dTermEs dTag.free_elims)
apply (frule_tac [2] dOcc_dAbst_lemma1)
apply (erule_tac [4] dOcc_dAbstE)
apply (erule_tac [2] dB_type [THEN dPropD1]
       | rule_tac [2] nat_0I)+
apply (blast intro!: LFreeIn_LTermIs elim!: dTag.free_elims)+
done

lemma dBoundBy_imp_LBoundBy:
  assumes prem1: "dBoundBy(<l, T>, <m, U>, dB(M))"
  and prem2: "M: LTerm"
  shows "EX T U. LBoundBy(<l, T>, <m, U>, M)"
apply (rule prem1 [THEN rev_mp])
apply (rule_tac x="m" in spec)
apply (rule_tac x="l" in spec)
apply (rule prem2 [THEN LTerm.induct])
apply (simp_all only: dB_eqns)
apply (safe elim!: dBoundBy_dTermEs dTag.free_elims)
apply (subgoal_tac "EX T. <m, T>: dOcc(dB(M))")
apply (erule_tac [2] dOcc_dAbstE)
apply (rule_tac [5] exI)
apply (rule_tac [4] exI)
apply (erule_tac [2] asm_rl 
       | rule_tac [2] dB_type [THEN dPropD1] nat_0I)+
apply (erule exE)
apply (rule_tac n1="0" and x1="x" in dLamDeg_dAbst_lemma [THEN revcut_rl])
apply (erule dB_type [THEN dPropD1])
apply (assumption | rule nat_0I)+
apply (rotate_tac 6)
apply simp
apply (drule dOcc_dAbst_lemma3 [THEN dFreeIn_imp_LFreeIn])
apply (assumption | rule dB_type)+
apply (rule exI [THEN exI])
apply (erule LBoundBy_LLamI1)
apply (drule dBoundBy_dAbstD)
apply (assumption | rule dB_type [THEN dPropD1] nat_0I)+
apply (drule_tac [3] spec [THEN spec, THEN mp], erule_tac [3] asm_rl)
apply (drule_tac [2] spec [THEN spec, THEN mp], erule_tac [2] asm_rl)
apply (drule_tac [1] spec [THEN spec, THEN mp], erule_tac [1] asm_rl)
apply safe
apply (assumption | rule exI [THEN exI]
       | erule LBoundBy_LTermIs)+
done

lemma LBoundBy_imp_dBoundBy:
  assumes prem1: "LBoundBy(<l, T>, <m, U>, M)"
  shows "EX T U. dBoundBy(<l, T>, <m, U>, dB(M))"
apply (rule prem1 [THEN rev_mp])
apply (rule_tac x="m" in spec)
apply (rule_tac x="l" in spec)
apply (rule prem1 [THEN LBoundByD1, THEN LBindingD1, THEN LTerm.induct])
apply (simp_all only: dB_eqns)
apply (safe elim!: LBoundBy_LTermEs LTag.free_elims)
apply (drule LFreeIn_imp_dFreeIn)
apply (rule exI [THEN exI])
apply (rule dBoundBy_dLamI1)
apply (erule_tac [3] dOcc_dAbstI1)
apply (rule_tac [2] add_0 [THEN ssubst])
apply (assumption | rule dAbst_type dB_type [THEN dPropD1]
         dLamDeg_dAbst_lemma nat_0I dLamDeg_type)+
apply (drule_tac [3] spec [THEN spec, THEN mp], erule_tac [3] asm_rl)
apply (drule_tac [2] spec [THEN spec, THEN mp], erule_tac [2] asm_rl)
apply (drule_tac [1] spec [THEN spec, THEN mp], erule_tac [1] asm_rl)
apply safe
apply (assumption | rule dBoundBy_dTermIs dBoundBy_dAbstI
         nat_0I dB_type [THEN dPropD1] exI)+
done

lemma dOcc_TdLam_imp_LOcc_TLLam:
  assumes major: "<l, TdLam>: dOcc(dB(M))"
  and prem: "M: LTerm"
  shows "EX x. <l, TLLam(x)>: LOcc(M)"
apply (rule major [THEN rev_mp])
apply (rule_tac x="l" in spec)
apply (rule prem [THEN LTerm.induct])
apply (simp_all only: dB_eqns)
apply (safe elim!: dOcc_dTermEs dOcc_dAbstE dTag.free_elims)
apply (erule_tac [2] asm_rl 
       | rule_tac [2] dB_type [THEN dPropD1] nat_0I)+
apply (drule_tac [4] spec [THEN mp], erule_tac [4] asm_rl)
apply (drule_tac [3] spec [THEN mp], erule_tac [3] asm_rl)
apply (drule_tac [2] spec [THEN mp], erule_tac [2] asm_rl)
apply safe
apply (assumption | rule exI LOcc_LTermIs)+
done

lemma LOcc_TLLam_imp_dOcc_TdLam:
  assumes major: "<l, TLLam(x)>: LOcc(M)"
  and prem: "M: LTerm"
  shows "<l, TdLam>: dOcc(dB(M))"
apply (rule major [THEN rev_mp])
apply (rule_tac x="l" in spec)
apply (rule prem [THEN LTerm.induct])
apply (simp_all only: dB_eqns)
apply (safe elim!: LOcc_LTermEs LTag.free_elims)
apply (drule_tac [4] spec [THEN mp], erule_tac [4] asm_rl)
apply (drule_tac [3] spec [THEN mp], erule_tac [3] asm_rl)
apply (drule_tac [2] spec [THEN mp], erule_tac [2] asm_rl)
apply (rule_tac [2] dOcc_dTermIs)
apply (erule_tac [2] dOcc_dAbstI2)
prefer 2 apply (blast elim!: dTag.free_elims)
apply (assumption | rule exI dB_type [THEN dPropD1] nat_0I
         dOcc_dTermIs)+
done

lemma dOcc_TdApp_imp_LOcc_TLApp:
  assumes major: "<l, TdApp>: dOcc(dB(M))"
  and prem: "M: LTerm"
  shows "<l, TLApp>: LOcc(M)"
apply (rule major [THEN rev_mp])
apply (rule_tac x="l" in spec)
apply (rule prem [THEN LTerm.induct])
apply (simp_all only: dB_eqns)
apply (safe elim!: dOcc_dTermEs dOcc_dAbstE dTag.free_elims)
apply (assumption | rule dB_type [THEN dPropD1] nat_0I)+
apply (drule_tac [4] spec [THEN mp], erule_tac [4] asm_rl)
apply (drule_tac [3] spec [THEN mp], erule_tac [3] asm_rl)
apply (drule_tac [1] spec [THEN mp], erule_tac [1] asm_rl)
apply (assumption | rule exI LOcc_LTermIs)+
done

lemma LOcc_TLApp_imp_dOcc_TdApp:
  assumes major: "<l, TLApp>: LOcc(M)"
  and prem: "M: LTerm"
  shows "<l, TdApp>: dOcc(dB(M))"
apply (rule major [THEN rev_mp])
apply (rule_tac x="l" in spec)
apply (rule prem [THEN LTerm.induct])
apply (simp_all only: dB_eqns)
apply (safe elim!: LOcc_LTermEs LTag.free_elims)
apply (drule_tac [4] spec [THEN mp], erule_tac [4] asm_rl)
apply (drule_tac [3] spec [THEN mp], erule_tac [3] asm_rl)
apply (drule_tac [1] spec [THEN mp], erule_tac [1] asm_rl)
apply (rule dOcc_dTermIs)
apply (erule dOcc_dAbstI2)
apply (blast elim!: dTag.free_elims)
apply (assumption | rule exI dB_type [THEN dPropD1] nat_0I
         dOcc_dTermIs)+
done

lemma LAlpha_imp_dAlpha:
  assumes major: "LAlpha(M, N)"
  shows "dAlpha(dB(M), dB(N))"
apply (insert major [THEN LAlphaD1, THEN LSkeltonEqD1]
              major [THEN LAlphaD1, THEN LSkeltonEqD2])
apply (rule dAlpha_dPropI)
apply (assumption | rule dB_type)+
apply safe
apply (drule_tac [8] dBoundBy_imp_LBoundBy)
apply (drule_tac [7] dBoundBy_imp_LBoundBy)
apply (drule_tac [6] dFreeIn_imp_LFreeIn)
apply (drule_tac [5] dFreeIn_imp_LFreeIn)
apply (drule_tac [4] dOcc_TdApp_imp_LOcc_TLApp)
apply (drule_tac [3] dOcc_TdApp_imp_LOcc_TLApp)
apply (drule_tac [2] dOcc_TdLam_imp_LOcc_TLLam)
apply (drule_tac [1] dOcc_TdLam_imp_LOcc_TLLam)
apply safe
apply (drule_tac [8] major [THEN LAlpha_sym, THEN LAlphaD3])
apply (drule_tac [7] major [THEN LAlphaD3])
apply (drule_tac [6] major [THEN LAlpha_sym, THEN LAlphaD2])
apply (drule_tac [5] major [THEN LAlphaD2])
apply (drule_tac [4] major [THEN LAlpha_sym, THEN LAlphaD1,
                            THEN LSkeltonEq_TLAppD])
apply (drule_tac [3] major [THEN LAlphaD1,
                            THEN LSkeltonEq_TLAppD])
apply (drule_tac [2] major [THEN LAlpha_sym, THEN LAlphaD1,
                            THEN LSkeltonEq_TLLamD])
apply (drule_tac [1] major [THEN LAlphaD1,
                            THEN LSkeltonEq_TLLamD])
apply safe
apply (drule_tac [8] LBoundBy_imp_dBoundBy)
apply (drule_tac [7] LBoundBy_imp_dBoundBy)
apply (drule_tac [6] LFreeIn_imp_dFreeIn)
apply (drule_tac [5] LFreeIn_imp_dFreeIn)
apply (drule_tac [4] LOcc_TLApp_imp_dOcc_TdApp)
apply (drule_tac [3] LOcc_TLApp_imp_dOcc_TdApp)
apply (drule_tac [2] LOcc_TLLam_imp_dOcc_TdLam)
apply (drule_tac [1] LOcc_TLLam_imp_dOcc_TdLam)
apply safe
apply (blast elim!: dBoundByE intro: dBoundByI)+
done

lemma dAlpha_imp_LAlpha:
  assumes major: "dAlpha(dB(M), dB(N))"
  and prem1: "M: LTerm"
  and prem2: "N: LTerm"
  shows "LAlpha(M, N)"
apply (insert prem1 prem2)
apply (rule LAlphaI2)
apply safe
apply (drule_tac [8] LBoundBy_imp_dBoundBy)
apply (drule_tac [7] LBoundBy_imp_dBoundBy)
apply (drule_tac [6] LFreeIn_imp_dFreeIn)
apply (drule_tac [5] LFreeIn_imp_dFreeIn)
apply (drule_tac [4] LOcc_TLApp_imp_dOcc_TdApp)
apply (drule_tac [3] LOcc_TLApp_imp_dOcc_TdApp)
apply (drule_tac [2] LOcc_TLLam_imp_dOcc_TdLam)
apply (drule_tac [1] LOcc_TLLam_imp_dOcc_TdLam)
apply safe
apply (drule_tac [8] major [THEN dAlpha_sym, THEN dAlpha_dBoundByD])
apply (drule_tac [7] major [THEN dAlpha_dBoundByD])
apply (drule_tac [6] major [THEN dAlpha_sym, THEN dAlphaD2])
apply (drule_tac [5] major [THEN dAlphaD2])
apply (drule_tac [4] major [THEN dAlpha_sym, THEN dAlphaD1,
                            THEN dSkeltonEq_TdAppD])
apply (drule_tac [3] major [THEN dAlphaD1,
                            THEN dSkeltonEq_TdAppD])
apply (drule_tac [2] major [THEN dAlpha_sym, THEN dAlphaD1,
                            THEN dSkeltonEq_TdLamD])
apply (drule_tac [1] major [THEN dAlphaD1,
                            THEN dSkeltonEq_TdLamD])
apply (drule_tac [8] dBoundBy_imp_LBoundBy)
apply (drule_tac [7] dBoundBy_imp_LBoundBy)
apply (drule_tac [6] dFreeIn_imp_LFreeIn)
apply (drule_tac [5] dFreeIn_imp_LFreeIn)
apply (drule_tac [4] dOcc_TdApp_imp_LOcc_TLApp)
apply (drule_tac [3] dOcc_TdApp_imp_LOcc_TLApp)
apply (drule_tac [2] dOcc_TdLam_imp_LOcc_TLLam)
apply (drule_tac [1] dOcc_TdLam_imp_LOcc_TLLam)
apply safe
apply (blast elim!: LBoundByE intro: LBoundByI)+
done

(** Now, we can prove correspondence between our alpha-equivarence, LAlpha,
    and equivarence under the de Bruijn notation, LAlpha3. **)

lemma LAlpha3_iff_LAlpha:
  "LAlpha3(M, N) <-> LAlpha(M, N)"
apply (unfold LAlpha3_def)
apply (rule iffI)
apply (erule conjE)+
apply (rule dAlpha_imp_LAlpha)
apply simp
apply (rule dAlpha_refl)
apply (assumption | rule dB_type [THEN dPropD1])+
apply (frule LAlphaD1 [THEN LSkeltonEqD1])
apply (frule LAlphaD1 [THEN LSkeltonEqD2])
apply (drule LAlpha_imp_dAlpha [THEN dAlpha_imp_dProp_eq])
apply (assumption | rule dB_type conjI)+
done

lemma LAlpha3D1:
  "LAlpha3(M, N) ==> M: LTerm"
apply (unfold LAlpha3_def)
apply (erule conjunct1)
done

lemma LAlpha3D2:
  "LAlpha3(M, N) ==> N: LTerm"
apply (unfold LAlpha3_def)
apply (erule conjunct2 [THEN conjunct1])
done

lemma LAlpha3D3:
  "LAlpha3(M, N) ==> dB(M) = dB(N)"
apply (unfold LAlpha3_def)
apply (erule conjunct2 [THEN conjunct2])
done

lemmas LAlpha_imp_dB_eq = LAlpha3_iff_LAlpha [THEN iffD2,
  THEN LAlpha3D3, rule_format]

lemmas dTerm_def_Terms_depth_induct = def_Terms_depth_induct [OF
  dTerm_Occ_cons_cond dTerm_Occ_ind_cond dOccinv_def]

lemma dProp_LTerm_lemma:
  assumes infv: "Infinite(LVariable)"
  and prem: "M: dProp"
  shows "EX M': LTerm. M = dB(M')"
apply (rule prem [THEN rev_mp])
apply (rule prem [THEN dPropD1, THEN dTerm_def_Terms_depth_induct])
apply (erule dTerm.cases)
prefer 4 apply hypsubst
prefer 4 apply hypsubst
defer 1
defer 1
apply (frule_tac [4] depth_ind_dApp1)
apply (frule_tac [6] depth_ind_dApp2)
apply (frule_tac [3] depth_ind_dLam)
apply (rule_tac [4] InfiniteE [OF infv dFV_Fin])
prefer 4 apply assumption
apply (safe elim!: dProp_dTermEs)
apply (drule_tac [3] M="Ma" and x="x" and n="0" in
         depth_ind_dSubst_dVar)
apply (frule_tac [6] M="Ma" and N="dVar(x)" in
         dDeg_dSubst_lemma3)
apply (erule_tac [3] asm_rl | rule_tac [3] nat_0I dProp_dVarI)+
apply (rule_tac x="LVar(x)" in bexI)
apply (simp only: dB_eqns)
apply (assumption | rule LTerm.intros)+
apply (frule_tac [3] x="Ma" in bspec)
apply (drule_tac [4] x="N" in bspec)
apply (drule_tac [2] x="dSubst(Ma, 0, dVar(x))" in bspec)
apply (drule_tac [1] x="Ma" in bspec)
prefer 3
prefer 5
prefer 6
apply (assumption | rule dSubst_type nat_0I dTerm.intros)+
apply (drule_tac [3] mp [THEN mp], erule_tac [3] asm_rl,
       erule_tac [3] asm_rl)+
apply (drule_tac [2] mp [THEN mp], erule_tac [2] asm_rl,
       erule_tac [2] asm_rl)+
apply (drule_tac [1] mp [THEN mp], erule_tac [1] asm_rl,
       erule_tac [1] asm_rl)+
apply safe
apply (rule_tac [3] x="LApp(M', M'a)" in bexI)
apply (rule_tac [2] x="LLam(x, M')" in bexI)
apply (rule_tac [1] x="LLam(x, M')" in bexI)
apply safe
apply (drule_tac [2] sym)
apply (drule_tac [2] sym)
apply (frule dDeg_dAbst_lemma1)
apply (assumption | rule nat_0I)+
apply (simp_all add: dB_eqns dAbst_dSubst_lemma)
done


(** LFV and dFV **)
lemma LFV_eq_dFV_dB:
  assumes major: "M: LTerm"
  shows "LFV(M) = dFV(dB(M))"
apply (rule major [THEN LTerm.induct])
apply (simp_all add: dB_eqns dB_type [THEN dPropD1]
         dFV_dAbst dAbst_type)
done


(** isSubst **)
lemma dsubst_lemma1:
  "[| x ~: dFV(M); dDeg(M) le n;
     M: dTerm; n: nat; N: dTerm
   |] ==> dSubst(dAbst(M, x, n), n, N) = M"
apply (rule dDeg_dAbst_lemma1 [THEN ssubst])
apply (rule_tac [4] dDeg_dSubst_lemma1)
apply assumption+
done

lemma dsubst_lemma2:
  assumes major: "x ~: dFV(N)"
  and sub: "dDeg(M) le n"
  and prem0: "x ~= y"
  and prem1: "M: dTerm"
  and prem2: "n: nat"
  and prem3: "N: dTerm"
  shows "dSubst(dAbst(dAbst(M, x, n), y, succ(n)), succ(n), N)
          = dAbst(dSubst(dAbst(M, y, n), n, N), x, n)"
apply (insert prem0)
apply (rule sub [THEN rev_mp])
apply (rule major [THEN rev_mp])
apply (rule prem2 [THEN [2] bspec])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem1 [THEN dTerm.induct])
apply (rule_tac [4] ballI [THEN ballI])
apply (rule_tac [3] ballI [THEN ballI])
apply (rule_tac [2] ballI [THEN ballI])
apply (rule_tac [1] ballI [THEN ballI])
apply (case_tac [2] "xaa = n")
apply (case_tac "x = xa")
apply (case_tac [2] "y = xa")
apply (case_tac "y = xa")
apply (simp_all add: dDeg_dAbst_lemma1 succ_neq_self_simps
        split del: split_if del: ball_simps)
apply safe
apply (erule_tac [2] bspec [THEN bspec, THEN mp, THEN mp, THEN function_apply_eq])
prefer 4 apply (simp add: dFV_dLift_iff)
apply (subgoal_tac "succ(xaa) ~= n" "~ succ(xaa) < n")
apply (simp split del: split_if)
apply (safe intro!: dLift_type)
apply (drule_tac [2] leI [THEN succ_le_iff [THEN iffD1]])
apply (erule_tac [2] lt_irrefl)
apply (drule lt_trans, assumption)
apply (drule leI [THEN succ_le_iff [THEN iffD1]])
apply (erule lt_irrefl)
done

lemma Lsubst_eq_dsubst:
  assumes major: "LFreeForIn(B, x, A)"
  shows "dB(Lsubst(A, x, B)) = dsubst(dB(A), x, dB(B))"
apply (rule major [THEN rev_mp])
apply (rule major [THEN LFreeForInD3, THEN LTerm.induct])
apply (rule_tac [3] impI, erule_tac [3] LFreeForIn_LTermEs)
apply (rule_tac [2] impI, erule_tac [2] LFreeForIn_LTermEs)
apply (rule_tac [1] impI, erule_tac [1] LFreeForIn_LTermEs)
apply (subgoal_tac [4] "LFreeForIn(B, x, M)")
apply (rule_tac [5] LFreeForInI)
apply (erule_tac [8] notE, erule_tac [8] LFV_I)
apply (erule_tac [5] asm_rl)+
apply (drule_tac [5] mp, erule_tac [5] asm_rl)+
apply (drule_tac [4] mp, erule_tac [4] asm_rl)+
apply (drule_tac [3] mp, erule_tac [3] asm_rl)+
prefer 2 apply hypsubst
prefer 2
apply (drule_tac [5] LFreeForInD1)+
apply (drule_tac [4] LFreeForInD1)+
apply (drule_tac [3] LFreeForInD1)+
apply (case_tac "x = xa")
prefer 2
apply (simp_all add: dB_eqns)
apply (simp_all add: dsubst_def dB_type [THEN dPropD1]
        dB_type [THEN dPropD2] dDeg_dLift_lemma1)
apply (rule_tac [2] dsubst_lemma2 [THEN sym, THEN function_apply_eq])
apply (rule_tac [8] dsubst_lemma1 [THEN sym, THEN function_apply_eq])
apply (rule_tac [1] dsubst_lemma1 [THEN sym, THEN function_apply_eq])
prefer 3
prefer 4
prefer 5
prefer 9
prefer 10
prefer 11
prefer 14
prefer 15
prefer 16
apply (assumption | rule dAbst_type dB_type dPropD1 nat_succI
         nat_0I)+
prefer 5 apply blast
apply (erule_tac [4] dB_type [THEN dPropD2, THEN ssubst])
apply (rule_tac [4] Ord_0 [THEN le_refl])
apply (rule_tac [4] notI, erule_tac [4] dFV_E)
apply (rule_tac [3] notI, erule_tac [3] dFV_E)
apply (rule_tac [1] notI, erule_tac [1] dFV_E)
apply (drule_tac [3] dFreeIn_imp_LFreeIn)
apply (erule_tac [4] notE, erule_tac [4] LFV_I)
apply (erule_tac [4] dOcc_dAbstE)
apply (drule dOcc_dAbst_lemma1)
prefer 3 apply blast
prefer 7 apply (blast elim!: dTag.free_elims)
apply (drule_tac [7] dFreeIn_imp_LFreeIn)
apply (erule_tac [8] notE, erule_tac [8] LFV_I)
prefer 4
prefer 5
prefer 6
prefer 7
apply (assumption | rule dB_type dPropD1 nat_succI nat_0I)+
apply (erule_tac [2] dB_type [THEN dPropE])+
apply (erule_tac [1] dB_type [THEN dPropE])+
apply (case_tac [2] "xa: dFV(dB(M))")
apply (case_tac [1] "x: dFV(dB(M))")
apply (simp_all add: dDeg_dAbst_lemma1 dDeg_dAbst_lemma2)
done

lemma isSubst1_isSubst2_iff:
  assumes infv: "Infinite(LVariable)"
  shows "isSubst1(A, x, B, C) <-> isSubst2(A, x, B, C)"
apply (unfold isSubst1_def isSubst2_def)
apply safe
apply (erule LAlphaD1 [THEN LSkeltonEqD1])
apply (erule LFreeForInD1)
apply (erule LAlphaD1 [THEN LSkeltonEqD2])
apply (erule LFreeForInD2)
apply (frule_tac [2] M="A" and N="B" in
         infv [THEN Infinite_LVariable_LAlpha_lemma])
apply (erule_tac [2] asm_rl)+
apply safe
apply (rule_tac [2] exI)
apply (erule_tac [2] asm_rl | rule_tac [2] conjI)+
apply (simp_all only: LAlpha3_iff_LAlpha [THEN iff_sym])
apply (unfold LAlpha3_def)
apply safe
prefer 2
apply (assumption | rule Lsubst_type)+
apply (rotate_tac [2] 9)
apply (simp_all add: Lsubst_eq_dsubst)
done

end
