(*
    File:        SndLBeta.thy
    Time-stamp:  <2016-01-06T17:03:46Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory SndLBeta imports LBeta begin

consts
  
  SndLBeta1 :: i
  
inductive
  domains "SndLBeta1" <= "LTerm * LTerm"
  
  intros
    baseI: "LFreeForIn(B, x, A) ==> 
            <LApp(LLam(x, A), B), Lsubst(A, x, B)>: SndLBeta1"

    LLamI: "[| <M, M'>: SndLBeta1;  x: LVariable |] ==> 
            <LLam(x, M), LLam(x, M')>: SndLBeta1"
  
    LAppI1: "[| <A, A'>: SndLBeta1;  B: LTerm |] ==> 
             <LApp(A, B), LApp(A', B)>: SndLBeta1"
    
    LAppI2: "[| <B, B'>: SndLBeta1;  A: LTerm |] ==> 
             <LApp(A, B), LApp(A, B')>: SndLBeta1"

  type_intros LTerm.intros SigmaI nat_0I Lsubst_type
  type_elims SigmaE2 LFreeForInE

lemma SndLBeta1_LBeta1:
  "<M, N>: SndLBeta1 ==> LBeta1(M, N)"
apply (erule SndLBeta1.induct)
apply (assumption | rule LBeta1_baseI LBeta1_LLamI
         LBeta1_LAppI1 LBeta1_LAppI2)+
done

lemma LBeta1_SndLBeta1:
  assumes prem: "LBeta1(M, N)"
  shows "<M, N>: SndLBeta1"
apply (rule prem [THEN rev_mp])
apply (rule prem [THEN LBeta1_type2, THEN [2] bspec])
apply (rule prem [THEN LBeta1_type1, THEN LTerm.induct])
apply (safe elim!: LBeta1_LTermEs LTerm_typeEs)
apply (drule_tac [4] bspec [THEN mp], erule_tac [4] asm_rl,
       erule_tac [4] asm_rl)
apply (drule_tac [3] bspec [THEN mp], erule_tac [3] asm_rl,
       erule_tac [3] asm_rl)
apply (drule_tac [1] bspec [THEN mp], erule_tac [1] asm_rl,
       erule_tac [1] asm_rl)
apply (assumption | erule SndLBeta1.intros)+
done

lemma SndLBeta1_iff_LBeta1:
  "<M, N> : SndLBeta1 <-> LBeta1(M, N)"
apply (rule iffI)
apply (erule SndLBeta1_LBeta1)
apply (erule LBeta1_SndLBeta1)
done

end
