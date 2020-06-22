(*
    File:        dBeta.thy
    Time-stamp:  <2020-06-22T04:37:29Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory dBeta imports dLambda begin

consts
  dBeta1Rel :: i
inductive
  domains "dBeta1Rel" <= "dTerm * dTerm"
  intros
    baseI: "[| M: dTerm; N: dTerm |] ==>
               <dApp(dLam(M), N), dSubst(M, 0, N)>: dBeta1Rel"
    dLamI: "<M, M'>: dBeta1Rel ==> <dLam(M), dLam(M')>: dBeta1Rel"
  
    dAppI1: "[| <M, M'>: dBeta1Rel; N: dTerm |] ==>
                 <dApp(M, N), dApp(M', N)>: dBeta1Rel"
    
    dAppI2: "[| M: dTerm; <N, N'>: dBeta1Rel |] ==>
             <dApp(M, N), dApp(M, N')>: dBeta1Rel"
  type_intros dTerm.intros SigmaI nat_0I dSubst_type
  type_elims SigmaE2

definition dBeta1 :: "[i, i]=>o" where
"dBeta1(M, N) == <M, N>: dBeta1Rel"


lemma dBeta1Rel_induct:
  assumes major: "<M, N>: dBeta1Rel"
  and
   "!!M N. [| M : dTerm; N : dTerm |] ==>
           P(dApp(dLam(M), N), dSubst(M, 0, N))"
  and
   "!!M M'. [| <M, M'> : dBeta1Rel; P(M, M') |] ==>
           P(dLam(M), dLam(M'))"
  and
   "!!M M' N.  [| <M, M'> : dBeta1Rel; P(M, M'); N : dTerm |] ==>
           P(dApp(M, N), dApp(M', N))"
  and
   "!!M N N'. [| M : dTerm; <N, N'> : dBeta1Rel; P(N, N') |] ==>
           P(dApp(M, N), dApp(M, N'))"
  shows "P(M, N)"
apply (rule_tac P="%x. P(x, N)" and b1="N" in fst_conv [THEN subst])
apply (rule_tac P="%x. P(fst(<M, N>), x)" and a1="M" in snd_conv [THEN subst])
apply (rule major [THEN dBeta1Rel.induct])
apply simp_all
apply (blast intro: assms)+
done

lemma dBeta1_type1:
  "dBeta1(M, N) ==> M: dTerm"
apply (unfold dBeta1_def)
apply (erule subsetD [OF dBeta1Rel.dom_subset, THEN SigmaD1])
done

lemma dBeta1_type2:
  "dBeta1(M, N) ==> N: dTerm"
apply (unfold dBeta1_def)
apply (erule subsetD [OF dBeta1Rel.dom_subset, THEN SigmaD2])
done

lemma dBeta1_baseI:
  "[| A: dTerm; B: dTerm |] ==>
        dBeta1(dApp(dLam(A), B), dSubst(A, 0, B))"
apply (unfold dBeta1_def)
apply (blast intro: dBeta1Rel.intros)
done

lemma dBeta1_dLamI:
  "dBeta1(M, M') ==> dBeta1(dLam(M), dLam(M'))"
apply (unfold dBeta1_def)
apply (blast intro: dBeta1Rel.intros)
done

lemma dBeta1_dAppI1:
  "[| dBeta1(M, M'); N: dTerm |] ==>
         dBeta1(dApp(M, N), dApp(M', N))"
apply (unfold dBeta1_def)
apply (blast intro: dBeta1Rel.intros)
done

lemma dBeta1_dAppI2:
  "[| M: dTerm; dBeta1(N, N') |] ==>
         dBeta1(dApp(M, N), dApp(M, N'))"
apply (unfold dBeta1_def)
apply (blast intro: dBeta1Rel.intros)
done

lemmas dBeta1_dTermIs = dBeta1_baseI dBeta1_dLamI
                        dBeta1_dAppI1 dBeta1_dAppI2

lemma dBeta1_dVarE:
  "dBeta1(dVar(x), N) ==> R"
apply (unfold dBeta1_def)
apply (erule dBeta1Rel.cases)
apply (safe elim!: dTerm.free_elims)
done

lemma dBeta1_dBoundE:
  "dBeta1(dBound(n), N) ==> R"
apply (unfold dBeta1_def)
apply (erule dBeta1Rel.cases)
apply (safe elim!: dTerm.free_elims)
done

lemma dBeta1_dLamE:
  "[| dBeta1(dLam(M), N);
      !!N'. [| dBeta1(M, N'); N = dLam(N')|] ==> R
   |] ==> R"
apply (unfold dBeta1_def)
apply (erule dBeta1Rel.cases)
apply (blast elim!: dTerm.free_elims)+
done

lemma dBeta1_dAppE:
  assumes major: "dBeta1(dApp(A, B), N)"
  and prem1:
     "!!x N'. [| N': dTerm; B: dTerm;
         A = dLam(N'); N = dSubst(N', 0, B) |] ==> R"
  and prem2:
     "!!A'. [| dBeta1(A, A'); B: dTerm; N = dApp(A', B) |] ==> R"
  and prem3:
     "!!B'. [| A: dTerm; dBeta1(B, B'); N = dApp(A, B') |] ==> R"
  shows "R"
apply (rule major [unfolded dBeta1_def, THEN dBeta1Rel.cases])
apply (rule_tac [4] prem3)
apply (rule_tac [3] prem2)
apply (rule_tac [1] prem1)
apply (unfold dBeta1_def)
apply (safe elim!: dTerm.free_elims)
prefer 2
prefer 3
prefer 5
prefer 7
apply (rule refl)+
apply assumption+
done

lemmas  dBeta1_dTermEs = dBeta1_dVarE dBeta1_dBoundE
                         dBeta1_dLamE dBeta1_dAppE

lemma dBeta1_dAbst:
  assumes major: "dBeta1(M, M')"
  and prem: "n: nat"
  shows "dBeta1(dAbst(M, x, n), dAbst(M', x, n))"
apply (rule major [THEN rev_mp])
apply (rule prem [THEN [2] bspec])
apply (rule major [THEN dBeta1_type2, THEN [2] bspec])
apply (rule major [THEN dBeta1_type1, THEN dTerm.induct])
apply (simp_all del: ball_simps)
apply (safe elim!: dBeta1_dTermEs dTerm_typeEs dTerm.free_elims)
apply (rotate_tac [2] 7)
apply (simp_all del: ball_simps add: dAbst_dSubst_lemma2)
apply (rule_tac [4] dBeta1_dAppI2)
apply (rule_tac [3] dBeta1_dAppI1)
apply (rule_tac [2] dBeta1_baseI)
apply (rule_tac [1] dBeta1_dLamI)
apply (erule_tac [7] bspec [THEN bspec, THEN mp])
apply (erule_tac [4] bspec [THEN bspec, THEN mp])
apply (erule_tac [1] bspec [THEN bspec, THEN mp])
apply (assumption | rule dAbst_type nat_succI)+
done

lemma dBeta1_dSubst:
  assumes major: "dBeta1(M, M')"
  and prem1: "N: dProp"
  and prem2: "n: nat"
  shows "dBeta1(dSubst(M, n, N), dSubst(M', n, N))"
apply (rule prem1 [THEN dPropE])
apply (rule major [THEN rev_mp])
apply (rule prem2 [THEN [2] bspec])
apply (rule major [THEN dBeta1_type2, THEN [2] bspec])
apply (rule major [THEN dBeta1_type1, THEN dTerm.induct])
apply (simp_all del: ball_simps)
apply (safe elim!: dBeta1_dTermEs dTerm_typeEs dTerm.free_elims)
apply (rotate_tac [2] 8)
apply (simp_all del: ball_simps add: dDeg_dLift_lemma1
         dSubst_dSubst_lemma2)
apply (rule_tac [4] dBeta1_dAppI2)
apply (rule_tac [3] dBeta1_dAppI1)
apply (rule_tac [2] dBeta1_baseI)
apply (rule_tac [1] dBeta1_dLamI)
apply (erule_tac [7] bspec [THEN bspec, THEN mp])
apply (erule_tac [4] bspec [THEN bspec, THEN mp])
apply (erule_tac [1] bspec [THEN bspec, THEN mp])
apply (assumption | rule dSubst_type nat_succI)+
done

lemma dBeta1_dDeg_lemma:
  assumes major: "dBeta1(M, N)"
  shows "dDeg(N) \<le> dDeg(M)"
apply (rule major [THEN rev_mp])
apply (rule major [THEN dBeta1_type2, THEN [2] bspec])
apply (rule major [THEN dBeta1_type1, THEN dTerm.induct])
apply (safe elim!: dBeta1_dTermEs dTerm_typeEs)
apply (simp_all del: ball_simps)
apply (rule_tac [2] M1="N'" in dDeg_type [THEN natE])
prefer 3
apply (simp del: ball_simps add: dDeg_dSubst_lemma1)
apply (rule_tac [3] dDeg_dSubst_lemma2)
prefer 4 apply simp
apply (erule_tac [2] asm_rl | rule_tac [2] nat_0I)+
apply (drule_tac [3] bspec [THEN mp], erule_tac [3] dBeta1_type2,
       erule_tac [3] asm_rl)
apply (drule_tac [2] bspec [THEN mp], erule_tac [2] dBeta1_type2,
       erule_tac [2] asm_rl)
apply (drule_tac [1] bspec [THEN mp], erule_tac [1] dBeta1_type2,
       erule_tac [1] asm_rl)
apply (rule_tac M1="M" in dDeg_type [THEN natE])
apply (rotate_tac [2] 4)
apply (rotate_tac [3] 4)
prefer 2 apply simp
prefer 2 apply simp
apply safe
apply (erule_tac [1] le_trans)
apply (erule_tac [4] le_trans)
apply (assumption | rule Un_upper1_le Un_upper2_le
         nat_into_Ord dDeg_type)+
done

lemma dBeta1_dProp_lemma:
  assumes major: "dBeta1(M, N)"
  and prem: "M: dProp"
  shows "N: dProp"
apply (rule dPropI)
apply (rule major [THEN dBeta1_type2])
apply (insert prem [THEN dPropD2] major [THEN dBeta1_dDeg_lemma])
apply simp
done

lemma dBeta1_dFV_lemma:
  assumes major: "dBeta1(M, N)"
  shows "dFV(N) <= dFV(M)"
apply (rule major [THEN rev_mp])
apply (rule major [THEN dBeta1_type2, THEN [2] bspec])
apply (rule major [THEN dBeta1_type1, THEN dTerm.induct])
apply (safe elim!: dBeta1_dTermEs dTerm_typeEs)
apply (rotate_tac [3] 7)
apply (rotate_tac [4] 7)
apply simp_all
apply (drule_tac [4] bspec [THEN mp], erule_tac [5] asm_rl)
apply (drule_tac [3] bspec [THEN mp], erule_tac [4] asm_rl)
apply (drule_tac [1] bspec [THEN mp], erule_tac [2] asm_rl)
apply (erule_tac [3] dFV_dSubst_lemma)
prefer 3
prefer 4
prefer 5
prefer 6
prefer 8
apply (erule dBeta1_type2 | assumption | rule nat_0I)+
apply safe
apply (drule_tac [3] subsetD, erule_tac [3] asm_rl)
apply (drule_tac [2] subsetD, erule_tac [2] asm_rl)
apply (drule_tac [1] subsetD, erule_tac [1] asm_rl)
apply safe
done

end

