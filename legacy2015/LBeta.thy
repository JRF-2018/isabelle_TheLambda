(*
    File:        LBeta.thy
    Time-stamp:  <2016-01-02T15:01:15Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory LBeta imports LAlpha begin

definition LBeta1 :: "[i, i]=>o" where
"LBeta1(M, N) == M: LTerm &
    (EX u: LSub(M). EX l x A B. u = <l, LApp(LLam(x, A), B)> &
        LFreeForIn(B, x, A) &
        N = LOccinv(Occ_Graft1(LOcc(M), l, LOcc(Lsubst(A, x, B)))))"

definition LBV :: "i=>i" where
"LBV(M) == {x: LVariable. EX l. <l, TLLam(x)>: LOcc(M)}"


(** LBeta1 **)
lemma LBeta1_type1:
  "LBeta1(M, N) ==> M: LTerm"
apply (unfold LBeta1_def)
apply (erule conjunct1)
done

lemma LBeta1_type2:
  "LBeta1(M, N) ==> N: LTerm"
apply (unfold LBeta1_def)
apply safe
apply (rule LTerm_def_Occinv_type)
apply (rule Occ_Graft1_in_Occ_range)
apply (erule_tac [2] LFreeForInE)
apply (assumption | rule LOcc_in_Occ_range Lsubst_type)+
apply (unfold LSub_def)
apply (erule RepFunE)
apply (frule LOcc_domain [THEN subsetD])
apply assumption
apply (erule SigmaE)
apply hypsubst
apply simp
apply (erule domainI)
done

lemmas LTerm_def_Sub_rec = def_Sub_rec [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LOccinv_def
  LSub_def LTerm_Term_cons_inj_cond]

lemmas LTerm_def_Occinv_Occ = def_Occinv_Occ [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LOccinv_def]

lemma LBeta1_baseI:
  assumes major: "LFreeForIn(B, x, A)"
  shows "LBeta1(LApp(LLam(x, A), B), Lsubst(A, x, B))"
apply (unfold LBeta1_def)
apply (rule major [THEN LFreeForInE])
apply (assumption | rule conjI bexI exI refl major LTerm.intros)+
prefer 2 
apply (simp add: LTerm_def_Sub_rec LTerm_cons_eqns_sym)
apply (rule Occ_consI1)
apply (simp add: Occ_Graft1_Nil LTerm_def_Occinv_Occ)
done

lemmas LTerm_def_Sub_type = def_Sub_type [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LOccinv_def
  LSub_def]

lemmas LTerm_def_Occinv2 = def_Occinv2 [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LOccinv_def]

lemma LBeta1_LLamI:
  "[| LBeta1(M, M');  x: LVariable |] ==> LBeta1(LLam(x, M), LLam(x, M'))"
apply (unfold LBeta1_def)
apply safe
apply (assumption | rule bexI conjI refl exI LTerm.intros)+
prefer 2
apply (simp add: LTerm_def_Sub_rec LTerm_cons_eqns_sym)
apply (rule_tac a="0" in Occ_consI2)
apply simp
apply (simp add: LTerm_cons_eqns)
apply (subgoal_tac "A: LTerm" "B: LTerm" "xa: LVariable" "l: list(nat)"
        "Occ_Graft1(LOcc(LLam(x, M)), Cons(0, l), LOcc(Lsubst(A, xa, B)))
                  : Occ_range(LTag, LArity)")
defer 1
apply (rule Occ_Graft1_in_Occ_range)
apply (assumption | rule LOcc_in_Occ_range Lsubst_type LTerm.intros)+
apply (simp add: LTerm_Occ_Term_cons LTerm_cons_eqns_sym)
apply (simp only: LSub_def)
apply (erule RepFunE)
apply (frule LOcc_domain [THEN subsetD])
apply assumption
apply (erule SigmaE)
apply hypsubst
apply simp
apply (rule Occ_consI2 [THEN domainI])
apply simp
apply simp
apply (erule LTerm_def_Sub_type [THEN subsetD, THEN SigmaD1])
apply assumption
apply (erule LFreeForInE, assumption)+
apply (simp add: LTerm_Occ_Term_cons LTerm_cons_eqns_sym)
apply (rule Occ_Graft1_Occ_cons_Cons [THEN ssubst])
apply (simp_all add: LTerm_cons_eqns_sym)
apply (rule LTerm_def_Occinv2 [THEN trans, THEN sym])
apply (rule_tac P="%x. x: Occ_range(LTag, LArity)" in subst)
prefer 2 apply assumption
apply (rule Occ_Graft1_Occ_cons_Cons [THEN ssubst])
apply (simp_all add: LTerm_def_Occinv_Occ)
apply (assumption | rule Occ_Graft1_domain LOcc_domain Lsubst_type
        PowI list.intros LTag.intros)+
done

lemma LBeta1_LAppI1:
  "[| LBeta1(A, A');  B: LTerm |] ==> LBeta1(LApp(A, B), LApp(A', B))"
apply (unfold LBeta1_def)
apply safe
apply (assumption | rule bexI conjI refl exI LTerm.intros)+
prefer 2
apply (simp add: LTerm_def_Sub_rec LTerm_cons_eqns_sym)
apply (rule_tac a="0" in Occ_consI2)
apply simp
apply simp
apply (subgoal_tac "Aa: LTerm" "Ba: LTerm" "x: LVariable" "l: list(nat)"
         "Occ_Graft1(LOcc(LApp(A, B)), Cons(0, l), LOcc(Lsubst(Aa, x, Ba)))
                 : Occ_range(LTag, LArity)")
defer 1
apply (rule Occ_Graft1_in_Occ_range)
apply (assumption | rule LOcc_in_Occ_range Lsubst_type LTerm.intros)+
apply (simp add: LTerm_Occ_Term_cons LTerm_cons_eqns_sym)
apply (simp only: LSub_def)
apply (erule RepFunE)
apply (rule LOcc_domain [THEN subsetD, THEN SigmaE])
prefer 2 apply assumption
apply assumption
apply hypsubst
apply simp
apply (rule Occ_consI2 [THEN domainI])
apply simp
apply simp
apply (rule LTerm_def_Sub_type [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption
apply (erule LFreeForInE, assumption)+
apply (simp add: LTerm_Occ_Term_cons LTerm_cons_eqns_sym)
apply (rule Occ_Graft1_Occ_cons_Cons [THEN ssubst])
apply (simp_all add: LTerm_cons_eqns_sym)
apply (rule LTerm_def_Occinv2 [THEN trans, THEN sym])
apply (rule_tac P="%x. x: Occ_range(LTag, LArity)" in subst)
prefer 2 apply assumption
apply (rule Occ_Graft1_Occ_cons_Cons [THEN ssubst])
apply (simp_all add: LTerm_def_Occinv_Occ)
apply (assumption | rule conjI Occ_Graft1_domain LOcc_domain Lsubst_type
         PowI list.intros LTag.intros)+
done

lemma LBeta1_LAppI2:
  "[| LBeta1(B, B');  A: LTerm |] ==> LBeta1(LApp(A, B), LApp(A, B'))"
apply (unfold LBeta1_def)
apply safe
apply (assumption | rule bexI conjI refl exI LTerm.intros)+
prefer 2
apply (simp add: LTerm_def_Sub_rec LTerm_cons_eqns_sym)
apply (rule_tac a="1" in Occ_consI2)
apply simp
apply simp
apply (subgoal_tac "Aa: LTerm" "Ba: LTerm" "x: LVariable" "l: list(nat)"
         "Occ_Graft1(LOcc(LApp(A, B)), Cons(1, l), LOcc(Lsubst(Aa, x, Ba)))
                 : Occ_range(LTag, LArity)")
defer 1
apply (rule Occ_Graft1_in_Occ_range)
apply (assumption | rule LOcc_in_Occ_range Lsubst_type LTerm.intros)+
apply (simp add: LTerm_Occ_Term_cons LTerm_cons_eqns_sym)
apply (simp only: LSub_def)
apply (erule RepFunE)
apply (rule LOcc_domain [THEN subsetD, THEN SigmaE])
prefer 2 apply assumption
apply assumption
apply hypsubst
apply simp
apply (rule Occ_consI2 [THEN domainI])
apply simp
apply simp
apply (rule LTerm_def_Sub_type [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption
apply (erule LFreeForInE, assumption)+
apply (simp add: LTerm_Occ_Term_cons LTerm_cons_eqns_sym)
apply (rule Occ_Graft1_Occ_cons_Cons [THEN ssubst])
apply (simp_all add: LTerm_cons_eqns_sym)
apply (rule LTerm_def_Occinv2 [THEN trans, THEN sym])
apply (rule_tac P="%x. x: Occ_range(LTag, LArity)" in subst)
prefer 2 apply assumption
apply (rule Occ_Graft1_Occ_cons_Cons [THEN ssubst])
apply (simp_all add: LTerm_def_Occinv_Occ)
apply (assumption | rule conjI Occ_Graft1_domain LOcc_domain Lsubst_type
         PowI list.intros LTag.intros)+
done

lemma LBeta1_LVarE:
  "LBeta1(LVar(x), N) ==> R"
apply (unfold LBeta1_def)
apply (safe elim!: LTerm_typeEs)
apply (rotate_tac 2)
apply (simp add: LTerm_def_Sub_rec LTerm_cons_eqns_sym)
apply (simp only: LTerm_cons_eqns)
apply (erule Occ_consE2)
prefer 3 apply simp
apply (safe elim!: LTerm.free_elims)
done

lemma LBeta1_LLamE:
  assumes major: "LBeta1(LLam(x, M), N)"
  and prem:
   "!!N'. [| N = LLam(x, N'); LBeta1(M, N'); x: LVariable |] ==> R"
  shows "R"
apply (insert major)
apply (unfold LBeta1_def)
apply (erule_tac conjE bexE exE LTerm_typeEs)+
apply (rotate_tac 4)
apply hypsubst
apply (simp add: LTerm_def_Sub_rec LTerm_Occ_Term_cons
        LTerm_cons_eqns_sym)
apply (simp only: LTerm_cons_eqns)
apply (erule Occ_consE)
apply (blast elim!: LTerm.free_elims)
apply simp
apply (erule succE)
apply (erule_tac [2] emptyE)
apply (erule conjE)
apply hypsubst
apply simp

apply (rule prem [unfolded LBeta1_def])
apply (erule trans)
defer 1
apply (assumption | rule conjI refl bexI exI)+
apply (rule Occ_Graft1_Occ_cons_Cons [THEN ssubst])
apply simp_all
apply (rule LTerm_def_Sub_type [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption
apply (subgoal_tac "A: LTerm" "xa: LVariable" "B: LTerm"
         "Occ_Graft1(LOcc(M), m, LOcc(Lsubst(A, xa, B))):
             Occ_range(LTag, LArity)"
         "LOccinv(Occ_Graft1(LOcc(M), m, LOcc(Lsubst(A, xa, B)))):
                  LTerm")
defer 1
apply (rule_tac [2] Occ_Graft1_in_Occ_range)
apply (assumption | rule LOcc_in_Occ_range Lsubst_type
         LTerm_def_Occinv_type LTerm.intros)+
apply (simp only: LSub_def)
apply (erule RepFunE)
apply (rule LOcc_domain [THEN subsetD, THEN SigmaE])
prefer 2
apply assumption
prefer 2
apply hypsubst
apply simp
apply (erule domainI)
apply assumption
apply (erule LFreeForInE, assumption)+
apply (rule trans)
apply (rule_tac [2] LTerm_def_Occinv_Occ)
apply (rule_tac f="LOccinv" in function_apply_eq)
apply (simp_all add: LTerm_Occ_Term_cons LTerm_def_Occ_Occinv
         LTerm_cons_eqns_sym)
done

lemma LBeta1_LAppE:
  assumes major: "LBeta1(LApp(A, B), N)"
  and prem1:
     "!!x N'. [| A = LLam(x, N'); N = Lsubst(N', x, B);
              LFreeForIn(B, x, N') |] ==> R"
  and prem2:
     "!!A'. [| N = LApp(A',B); LBeta1(A, A'); B: LTerm |] ==> R"
  and prem3:
     "!!B'. [| N = LApp(A, B'); LBeta1(B, B'); A: LTerm |] ==> R"
  shows "R"
apply (insert major)
apply (unfold LBeta1_def)
apply (erule conjE bexE exE LTerm_typeEs)+
apply (rotate_tac 4)
apply hypsubst
apply (simp add: LTerm_def_Sub_rec LTerm_Occ_Term_cons
         LTerm_cons_eqns_sym)
apply (simp only: LTerm_cons_eqns)
apply (erule Occ_consE)
prefer 2
apply simp
defer 1
apply (erule_tac [2] succE)
apply (erule_tac [3] succE)
apply (rule_tac [3] prem2)
apply (rule_tac [2] prem3)
apply (rule_tac [1] prem1)
apply (unfold LBeta1_def)
apply (safe elim!: LTerm.free_elims LTerm_typeEs)
apply (rule refl)
apply (rule Occ_Graft1_Nil [THEN ssubst])
apply (rule Occ_cons_type)
apply (rule LTag.intros)
apply (assumption | rule Occ_cons_type LOcc_domain PowI
        Lsubst_type list.intros LTerm.intros)+
apply (simp add: LTerm_def_Occinv_Occ)
apply assumption
apply simp_all
prefer 2 apply (assumption | rule bexI exI conjI refl)+
prefer 3 apply (assumption | rule bexI exI conjI refl)+
apply (rule_tac [2] Occ_Graft1_Occ_cons_Cons [THEN ssubst])
apply (rule_tac [1] Occ_Graft1_Occ_cons_Cons [THEN ssubst])
apply simp_all
apply (rule LTerm_def_Sub_type [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption
apply (rule_tac [2] LTerm_def_Sub_type [THEN subsetD, THEN SigmaD1])
prefer 3 apply assumption
prefer 2 apply assumption

apply (subgoal_tac [2] "Aa: LTerm" "x: LVariable" "Ba: LTerm"
         "Occ_Graft1(LOcc(A), m, LOcc(Lsubst(Aa, x, Ba))):
             Occ_range(LTag, LArity)"
         "LOccinv(Occ_Graft1(LOcc(A), m, LOcc(Lsubst(Aa, x, Ba)))):
              LTerm")
apply (subgoal_tac [1] "Aa: LTerm" "x: LVariable" "Ba: LTerm"
         "Occ_Graft1(LOcc(B), m, LOcc(Lsubst(Aa, x, Ba))):
             Occ_range(LTag, LArity)"
         "LOccinv(Occ_Graft1(LOcc(B), m, LOcc(Lsubst(Aa, x, Ba)))):
              LTerm")
defer 1
apply (rule_tac [2] Occ_Graft1_in_Occ_range)
apply (assumption | rule LOcc_in_Occ_range Lsubst_type
         LTerm_def_Occinv_type LTerm.intros)+
apply (simp only: LSub_def)
apply (erule RepFunE)
apply (rule LOcc_domain [THEN subsetD, THEN SigmaE])
prefer 2 apply assumption
apply assumption
apply hypsubst
apply simp
apply (erule domainI)
apply (erule LFreeForInE, assumption)+
defer 1
apply (rule_tac [2] Occ_Graft1_in_Occ_range)
apply (assumption | rule LOcc_in_Occ_range Lsubst_type
         LTerm_def_Occinv_type LTerm.intros)+
apply (simp only: LSub_def)
apply (erule RepFunE)
apply (rule LOcc_domain [THEN subsetD, THEN SigmaE])
prefer 2 apply assumption
apply assumption
apply hypsubst
apply simp
apply (erule domainI)
apply (erule LFreeForInE, assumption)+
apply (rule_tac [2] trans)
apply (rule_tac [3] LTerm_def_Occinv_Occ)
apply (rule_tac [2] f="LOccinv" in function_apply_eq)
apply (rule trans)
apply (rule_tac [2] LTerm_def_Occinv_Occ)
apply (rule_tac f="LOccinv" in function_apply_eq)
apply (simp_all add: LTerm_Occ_Term_cons LTerm_def_Occ_Occinv
         LTerm_cons_eqns_sym)
done

lemmas LBeta1_LTermEs = LBeta1_LVarE LBeta1_LLamE LBeta1_LAppE

lemma LBeta1_redex_lemma:
  assumes infv: "Infinite(LVariable)"
  and major: "M: LTerm"
  and prem: "<l, LApp(LLam(x, A),B)>: LSub(M)"
  shows "EX N A'. LAlpha(M, N) & <l, LApp(LLam(x, A'), B)>: LSub(N) &
              LFreeForIn(B, x, A')"
apply (rule prem [THEN rev_mp])
apply (rule_tac x="l" in spec)
apply (rule major [THEN LTerm.induct])
apply (simp_all add: LTerm_def_Sub_rec LTerm_cons_eqns_sym)
apply (simp_all only: LTerm_cons_eqns)
apply (rule_tac [3] impI [THEN allI], erule_tac [3] Occ_consE2)
apply (rule_tac [2] impI [THEN allI], erule_tac [2] Occ_consE2)
apply (rule_tac [1] impI [THEN allI], erule_tac [1] Occ_consE2)
prefer 4
prefer 7
apply (assumption | rule LTerm_def_Sub_type [THEN PowI]
        list.intros)+
apply (simp_all add: le_succ_iff)
apply (safe elim!: LTerm.free_elims LTerm_typeEs)
apply simp_all
apply (rule_tac [2] infv [THEN Infinite_LVariable_LAlpha_lemma, THEN bexE])
apply (erule_tac [5] conjE)
apply (rule_tac [5] exI)
apply (rule_tac [5] conjI)
apply (rule_tac [6] exI)
apply (rule_tac [6] conjI)
prefer 7 apply assumption
apply (rule_tac [5] LAlpha_LAppI)
apply (rule_tac [5] LAlpha_LLamI1)
prefer 5 apply assumption
apply (erule_tac [2] asm_rl | rule_tac [2] LAlpha_refl)+
prefer 2 apply (simp add: LTerm_def_Sub_rec LTerm_cons_eqns_sym)
apply (rule Occ_consI1)

apply (drule_tac [3] spec [THEN mp], erule_tac [3] asm_rl)
apply (drule_tac [2] spec [THEN mp], erule_tac [2] asm_rl)
apply (drule_tac [1] spec [THEN mp], erule_tac [1] asm_rl)
apply safe

prefer 3
apply (intro exI conjI)
apply (assumption | rule LAlpha_LLamI1 LAlpha_LAppI LAlpha_refl)+
prefer 2 apply assumption
apply (frule LAlphaD1 [THEN LSkeltonEqD2])
apply (simp add: LTerm_def_Sub_rec LTerm_cons_eqns_sym)
apply (rule Occ_consI2)
apply simp
apply simp

prefer 2
apply (intro exI conjI)
apply (assumption | rule LAlpha_LLamI1 LAlpha_LAppI LAlpha_refl)+
prefer 2 apply assumption
apply (frule LAlphaD1 [THEN LSkeltonEqD2])
apply (simp add: LTerm_def_Sub_rec LTerm_cons_eqns_sym)
apply (rule Occ_consI2)
apply simp
apply simp

apply (intro exI conjI)
apply (assumption | rule LAlpha_LLamI1 LAlpha_LAppI LAlpha_refl)+
prefer 2 apply assumption
apply (frule LAlphaD1 [THEN LSkeltonEqD2])
apply (simp add: LTerm_def_Sub_rec LTerm_cons_eqns_sym)
apply (rule Occ_consI2)
apply simp
apply simp
done

lemma LFreeForIn_left_LsubstD1:
  assumes major: "LFreeForIn(Lsubst(A, x, B), y, M)"
  and prem1: "LFreeForIn(LVar(x), y, M)"
  and prem2: "LFreeForIn(B, x, A)"
  shows "LFreeForIn(A, y, M)"
apply (insert prem1 [THEN LFreeForInD1] prem1 [THEN LFreeForInD2]
              prem1 [THEN LFreeForInD3] prem2 [THEN LFreeForInD1]
              prem2 [THEN LFreeForInD2] prem2 [THEN LFreeForInD3])
apply (erule LTerm_typeEs)
apply (insert prem2)
apply (rule LFreeForInI)
apply (erule_tac [4] LFV_E)
apply (case_tac [4] "x = z")
prefer 4 apply hypsubst
defer 1
apply (rule_tac [4] major [THEN LFreeForInE])
apply (rule_tac [5] prem1 [THEN LFreeForInE])
apply (erule_tac [5] spec [THEN spec, THEN spec, THEN mp])
apply (erule_tac [4] spec [THEN spec, THEN spec, THEN mp])
apply safe
prefer 5 apply simp
apply (erule_tac [2] asm_rl)+
apply (rule LFV_I)
apply (rule LFreeIn_LsubstI1)
apply assumption+
done

lemma LFreeForIn_right_LsubstD:
  assumes major: "LFreeForIn(A, x, Lsubst(M, y, B))"
  and prem1: "LFreeForIn(B, y, M)"
  and prem2: "x: LFV(B)"
  shows "LFreeForIn(A, y, M)"
apply (insert major [THEN LFreeForInD1] major [THEN LFreeForInD2]
              major [THEN LFreeForInD3] prem1 [THEN LFreeForInD1]
              prem1 [THEN LFreeForInD2] prem1 [THEN LFreeForInD3])
apply (rule prem2 [THEN LFV_E])
apply (case_tac "y: LFV(M)")
prefer 2
apply (rule LFreeForInI)
apply (erule_tac [4] notE, erule_tac [4] LFV_I)
apply (rule_tac [4] LFreeForInI)
apply assumption+
apply (erule LFV_E)+
apply (rule major [THEN LFreeForInE])
apply (erule spec [THEN spec, THEN spec, THEN mp])
apply safe
apply (erule LFV_I)
apply (rule_tac [2] LOcc_LsubstI1)
prefer 3 apply assumption
prefer 2 apply (blast elim!: LFO_E LTag.free_elims)
apply (rule LFreeIn_LsubstI2)
apply (assumption | rule prem1 LFO_I)+
apply (erule initseg_appI3)
apply (erule LFreeInE2, erule LOcc_typeD1, assumption)
done

lemma LFreeIn_TLVar_leaf:
  assumes prem1: "LFreeIn(<l, T>, M)"
  and prem2: "<l @ m, U>: LOcc(M)"
  shows "m = [] & T = U"
apply (rule prem1 [THEN LFreeInE])
apply (frule prem2 [THEN [2] TLVar_leaf])
apply safe
apply (rule initseg_appI1)
apply (erule_tac [3] app_Nil_eqD1)
apply (frule_tac [2] prem2 [THEN LOcc_typeD1])
apply (erule_tac [2] app_typeD)
apply (assumption | erule LOcc_typeD1)+
done

lemma LFreeForIn_right_LsubstI1:
  assumes prem1: "LFreeForIn(N, x, A)"
  and prem2: "B: LTerm"
  and prem3: "x ~: LFV(B)"
  shows "LFreeForIn(N, x, Lsubst(A, y, B))"
apply (insert prem1 [THEN LFreeForInD1] prem1 [THEN LFreeForInD2]
              prem1 [THEN LFreeForInD3])
apply (insert prem2)
apply (assumption | rule Lsubst_type LFreeForInI)+
apply (safe elim!: LFreeIn_LsubstE initseg_right_appE
          initseg_left_appE LOcc_LsubstE LFV_E LFO_E2
          dest!: sym [THEN app_Nil_eqD1])
prefer 2
prefer 4
prefer 6
prefer 8
prefer 9
apply (erule LFreeInE2, erule LOcc_typeD1, assumption)+
prefer 2
prefer 3
prefer 4
prefer 6
apply (erule LFV_I [THEN prem3 [THEN notE]])+
apply (frule_tac [2] LFreeIn_TLVar_leaf, erule_tac [2] LFreeInE2,
       erule_tac [2] asm_rl)
prefer 2 apply (blast elim!: LTag.free_elims)
apply (rule prem1 [THEN LFreeForInE])
apply (erule spec [THEN spec, THEN spec, THEN mp])
apply (assumption | rule LFV_I conjI initseg_appI1)+
done

lemma LFreeForIn_left_LsubstI:
  assumes prem1: "LFreeForIn(A, x, M)"
  and prem2: "LFreeForIn(B, x, M)"
  shows "LFreeForIn(Lsubst(A, y, B), x, M)"
apply (insert prem1 [THEN LFreeForInD1] prem1 [THEN LFreeForInD2]
              prem1 [THEN LFreeForInD3] prem2 [THEN LFreeForInD1]
              prem2 [THEN LFreeForInD2] prem2 [THEN LFreeForInD3])
apply (assumption | rule Lsubst_type LFreeForInI)+
apply (safe elim!: LFreeIn_LsubstE LFV_E)
apply (rule prem1 [THEN LFreeForInE])
apply (erule spec [THEN spec, THEN spec, THEN mp])
apply (assumption | rule LFV_I conjI initseg_appI1)+
apply (rule prem2 [THEN LFreeForInE])
apply (erule spec [THEN spec, THEN spec, THEN mp])
apply (assumption | rule LFV_I conjI initseg_appI1)+
done

lemma LBeta1_LsubstI:
  assumes major: "LBeta1(M, M')"
  and prem1: "LFreeForIn(N, x, M)"
  and prem2: "LFreeForIn(N, x, M')"
  shows "LBeta1(Lsubst(M, x, N), Lsubst(M', x, N))"
apply (rule prem2 [THEN rev_mp])
apply (rule prem1 [THEN rev_mp])
apply (rule major [THEN rev_mp])
apply (rule major [THEN LBeta1_type2, THEN [2] bspec])
apply (rule major [THEN LBeta1_type1, THEN LTerm.induct])
apply (safe elim!: LBeta1_LTermEs LFreeForIn_LTermEs)
apply (subgoal_tac [8] "xaa ~= x")
prefer 9 apply blast
apply (simp_all add: Lsubst_lemma Lsubst_lemma4
        LFreeForInD1 LFreeForInD3)
apply (rule_tac [10] LBeta1_LAppI2)
apply (rule_tac [9] LBeta1_LAppI1)
apply (rule_tac [8] LBeta1_LLamI LBeta1_baseI)
apply (rule_tac [7] LBeta1_LLamI LBeta1_baseI)
apply (rule_tac [6] LBeta1_LLamI LBeta1_baseI)
apply (rule_tac [5] LBeta1_LLamI LBeta1_baseI)
apply (rule_tac [4] LBeta1_LLamI LBeta1_baseI)
apply (rule_tac [3] LBeta1_LLamI LBeta1_baseI)
apply (rule_tac [2] LBeta1_LLamI LBeta1_baseI)
apply (rule_tac [1] LBeta1_LLamI LBeta1_baseI)
prefer 1
prefer 2
prefer 4
prefer 6
prefer 8
prefer 9
prefer 10
prefer 15
prefer 17
apply (assumption | rule Lsubst_type 
       | erule LTerm_typeEs | erule LFreeForInD1)+
apply (simp_all add: LFreeForInD1 LFreeForInD3)
apply (drule_tac [2] bspec [THEN mp, THEN mp, THEN mp])
prefer 3 apply assumption
apply (erule_tac [2] LFreeForInD3)
apply (rule_tac [2] LFreeForInI)
apply (erule_tac [5] notE, erule_tac [5] LFV_I)
apply (erule_tac [2] asm_rl LFreeForInD1)+
apply (drule bspec [THEN mp, THEN mp])
prefer 2 apply assumption
apply (erule LBeta1_type2)
apply (rule LFreeForInI)
apply (erule_tac [4] notE, erule_tac [4] LFV_I)
apply (erule_tac [3] LBeta1_type2)
apply (erule_tac [1] LFreeForInD1)
apply assumption
apply (simp add: LBeta1_type2)
apply (rule_tac [2] LFreeForIn_right_LsubstI1)
apply (erule_tac [3] LFreeForInD1)
prefer 3 apply assumption
apply (case_tac [3] "x: LFV(Na)")
apply (case_tac [2] "x: LFV(Na)")
apply (case_tac [1] "x: LFV(Na)")
apply (simp_all add: LFreeForInD1)
apply (safe dest!: LFreeForIn_right_LsubstD)
apply (assumption | rule LFreeForIn_left_LsubstI)+
done


(** LBV **)
lemma LBV_I:
  "[| <l, TLLam(x)>: LOcc(M); M: LTerm |] ==> x: LBV(M)"
apply (unfold LBV_def)
apply (frule LOcc_typeD2)
apply assumption
apply (erule LTag_typeEs)
apply blast
done

lemma LBV_E:
  "[| x: LBV(M);
      !!l. [| <l, TLLam(x)>: LOcc(M); x: LVariable |] ==> R
   |] ==> R"
apply (unfold LBV_def)
apply blast
done

lemma LBV_LVar:
  "x: LVariable ==> LBV(LVar(x)) = 0"
apply (rule equalityI)
apply (blast elim!: LBV_E LOcc_LTermEs LTag.free_elims
           intro: LBV_I intro!: LOcc_LTermIs)+
done

lemma LBV_LLam:
  "[| x: LVariable; M: LTerm |] ==> LBV(LLam(x, M)) = cons(x, LBV(M))"
apply (rule equalityI)
apply (blast elim!: LBV_E LOcc_LTermEs LTag.free_elims
           intro: LBV_I intro!: LOcc_LTermIs)+
done

lemma LBV_LApp:
  "[| M: LTerm; N: LTerm |] ==> LBV(LApp(M, N)) = LBV(M) Un LBV(N)"
apply (rule equalityI)
apply (blast elim!: LBV_E LOcc_LTermEs LTag.free_elims
           intro: LBV_I intro!: LOcc_LTermIs)+
done

lemmas LBV_eqns = LBV_LVar LBV_LLam LBV_LApp

lemma LAV_eq_LFV_LBV:
  "M: LTerm ==> LAV(M) = LFV(M) Un LBV(M)"
apply (erule LTerm.induct)
apply (simp_all add: LBV_eqns)
apply (rule equalityI, blast, blast)+
done

lemma LBV_Lsubst1:
  assumes major: "M: LTerm"
  and prem1: "N: LTerm"
  and prem2: "x: LFV(M)"
  shows "LBV(Lsubst(M, x, N)) = LBV(M) Un LBV(N)"
apply (insert prem1)
apply (rule prem2 [THEN rev_mp])
apply (rule major [THEN LTerm.induct])
apply (case_tac [3] "x: LFV(M)")
apply (case_tac [3] "x: LFV(Na)")
apply (simp_all add: LBV_eqns)
apply blast+
done

lemma LBV_Lsubst2:
  "[| M: LTerm; N: LTerm |] ==> LBV(Lsubst(M, x, N)) <= LBV(M) Un LBV(N)"
apply (case_tac "x: LFV(M)")
apply (simp_all add: LBV_Lsubst1)
apply (rule Un_upper1)
done

lemma disjoint_LBV_LFV_imp_LFreeForIn:
  "[| LBV(M) Int LFV(N) = 0; M: LTerm; N: LTerm; x: LVariable |]
       ==> LFreeForIn(N, x, M)"
apply (assumption | rule LFreeForInI)+
apply (erule disjointE)
apply (assumption | rule LBV_I)+
done

lemma LFV_Fin:
  "M: LTerm ==> LFV(M): Fin(LVariable)"
apply (rule Fin_subset)
apply (assumption | rule LFV_subset_LAV LAV_Fin)+
done

lemma LBV_Fin:
  assumes major: "M: LTerm"
  shows "LBV(M): Fin(LVariable)"
apply (rule Fin_subset)
apply (rule_tac [2] major [THEN LAV_Fin])
apply (rule major [THEN LAV_eq_LFV_LBV, THEN ssubst])
apply (rule Un_upper2)
done

lemma Infinite_LVariable_LAlpha_lemma3:
  assumes infv: "Infinite(LVariable)"
  and major: "M: LTerm"
  and prem: "X: Fin(LVariable)"
  shows "EX M'. LAlpha(M, M') & LBV(M') Int X = 0"
apply (rule major [THEN LTerm.induct])
apply (rule exI)
apply (rule LAlpha_LVarI [THEN conjI])
apply assumption
apply (simp add: LBV_eqns)
apply safe
apply (frule LAlphaD1 [THEN LSkeltonEqD2])
apply (rule_tac F="X Un LAV(M') Un {x}" in infv [THEN InfiniteE])
apply (assumption | rule Fin_UnI LAV_Fin prem Fin.intros)+
apply (simp add: LAV_eq_LFV_LBV)
apply (erule conjE)+
apply (rule conjI [THEN exI])
apply (rule LAlpha_LLamI3)
prefer 3 apply assumption
apply (rule_tac [2] disjoint_LBV_LFV_imp_LFreeForIn)
prefer 2
apply simp
apply (rule disjointI)
apply blast
apply (assumption | rule LTerm.intros)+
apply (case_tac "x: LFV(M')")
prefer 2
apply (simp_all add: LBV_eqns LBV_Lsubst1)
apply (rule cons_eq [THEN subst])
apply (rule_tac [2] cons_eq [THEN subst])
apply (rule disjoint_UnI)
apply (rule_tac [3] disjoint_UnI)
apply (rule disjointI)
apply (rule_tac [3] disjointI)
prefer 2
prefer 4
apply assumption+
apply blast
apply blast
apply (rule conjI [THEN exI])
apply (assumption | rule LAlpha_LAppI)+
apply (simp add: LBV_eqns LAlphaD1 [THEN LSkeltonEqD2])
apply (assumption | rule disjoint_UnI)+
done

lemma LBeta1_LBV_lemma:
  assumes major: "LBeta1(M, N)"
  shows "LBV(N) <= LBV(M)"
apply (rule major [THEN rev_mp])
apply (rule major [THEN LBeta1_type2, THEN rev_bspec])
apply (rule major [THEN LBeta1_type1, THEN LTerm.induct])
apply (safe elim!: LBeta1_LTermEs LTerm_typeEs)
apply (case_tac [2] "xb: LFV(N')")
apply (rotate_tac [3] 5)
apply (rotate_tac [2] 6)
apply (rotate_tac [4] 5)
apply (rotate_tac [5] 5)
apply (simp_all add: LBV_eqns LBV_Lsubst1)
apply (drule_tac [3] bspec [THEN mp], erule_tac [3] LBeta1_type2,
       erule_tac [3] asm_rl)
apply (drule_tac [2] bspec [THEN mp], erule_tac [2] LBeta1_type2,
       erule_tac [2] asm_rl)
apply (drule_tac [1] bspec [THEN mp], erule_tac [1] LBeta1_type2,
       erule_tac [1] asm_rl)
apply safe
apply (erule swap, rule subsetD, assumption, assumption)
apply (erule subsetD, assumption)
apply (erule swap, rule subsetD, assumption, assumption)
done

lemma LBeta1_LFV_lemma:
  assumes major: "LBeta1(M, N)"
  shows "LFV(N) <= LFV(M)"
apply (rule major [THEN rev_mp])
apply (rule major [THEN LBeta1_type2, THEN [2] bspec])
apply (rule major [THEN LBeta1_type1, THEN LTerm.induct])
apply (safe elim!: LBeta1_LTermEs LTerm_typeEs)
apply (rotate_tac [3] 5)
apply (rotate_tac [4] 5)
apply simp_all
apply (drule_tac [4] bspec [THEN mp], erule_tac [4] LBeta1_type2,
       erule_tac [4] asm_rl)
apply (drule_tac [3] bspec [THEN mp], erule_tac [3] LBeta1_type2,
       erule_tac [3] asm_rl)
apply (drule_tac [1] bspec [THEN mp], erule_tac [1] LBeta1_type2,
       erule_tac [1] asm_rl)
apply (safe elim!: LFV_E LFreeIn_LsubstE LTag.free_elims)
apply (erule_tac [4] notE, erule_tac [4] LFV_I)
apply (erule_tac [3] notE, erule_tac [3] LFV_I)
apply (erule_tac [4] swap, rule_tac [4] subsetD,
       erule_tac [4] asm_rl, erule_tac [4] LFV_I)
apply (erule_tac [3] subsetD, erule_tac [3] LFV_I)
apply (erule_tac [1] subsetD, erule_tac [1] LFV_I)
apply (erule LFV_I)
done

lemma LBeta1_LAlpha_parallel_lemma:
  assumes infv: "Infinite(LVariable)"
  and major: "LBeta1(M, N)"
  and prem1: "X: Fin(LVariable)"
  shows "EX M' N'. LAlpha(M, M') & LAlpha(N, N') &
            LBV(M') Int X = 0  & LBeta1(M', N')"
apply (insert prem1)
apply (rule major [THEN rev_mp])
apply (rule major [THEN LBeta1_type2, THEN [2] bspec])
apply (rule major [THEN LBeta1_type1, THEN LTerm.induct])
apply (safe elim!: LBeta1_LTermEs)
apply (frule_tac [2] LFreeForInD2)
apply (frule_tac [2] LFreeForInD3)
apply (rule_tac [2] F="X Un LFV(N')" in infv [THEN InfiniteE])
apply (erule_tac [2] asm_rl | rule_tac [2] Fin_UnI prem1 LFV_Fin)+

apply (rule_tac [2] M1="N" and X1="X" in 
         infv [THEN Infinite_LVariable_LAlpha_lemma3, THEN revcut_rl])
apply (erule_tac [2] asm_rl | rule_tac [2] prem1)+
apply (erule_tac [2] exE)
apply (erule_tac [2] conjE)
apply (frule_tac [2] LAlphaD1 [THEN LSkeltonEqD2])
apply (rule_tac [2] M1="N'" and X1="X Un {xb} Un LFV(M')" in 
         infv [THEN Infinite_LVariable_LAlpha_lemma3, THEN revcut_rl])
apply (erule_tac [2] asm_rl | rule_tac [2] Fin.intros 
        Fin_UnI prem1 LFV_Fin)+
apply (erule_tac [2] exE)
apply (simp_all add: disjoint_Un_iff2 disjoint_cons_iff2)
apply (erule_tac [2] conjE)+
apply (frule_tac [2] N="M'a" in LAlphaD1 [THEN LSkeltonEqD2])

apply (subgoal_tac [2] "xb ~: LFV(M'a)" "LFreeForIn(M', xb, M'a)"
         "LFreeForIn(LVar(xb), xa, M'a)")
apply (rule_tac [3] disjoint_LBV_LFV_imp_LFreeForIn)
prefer 3 apply (simp add: disjoint_Un_iff2 disjoint_cons_iff2)
apply (erule_tac [3] asm_rl | rule_tac [3] LTerm.intros)+
apply (erule_tac [3] disjoint_LBV_LFV_imp_LFreeForIn)
apply (rule_tac [6] notI)
apply (erule_tac [6] LFV_E)
apply (drule_tac [6] LAlpha_sym [THEN LAlphaD2], erule_tac [6] asm_rl)
apply (erule_tac [6] notE, erule_tac [6] LFV_I)
apply (erule_tac [3] asm_rl)+

apply (rule_tac [2] conjI [THEN exI])
apply (rule_tac [3] exI)
apply (rule_tac [2] LAlpha_LAppI)
apply (rule_tac [2] LAlpha_LLamI3)
apply (erule_tac [3] asm_rl)
apply (erule_tac [2] asm_rl | rule_tac [2] conjI)+
apply (rule_tac [3] conjI)
apply (rule_tac [4] LBeta1_baseI)
apply (case_tac [3] "xa: LFV(M'a)")
prefer 4 apply (simp add: LBV_eqns
                 disjoint_Un_iff disjoint_cons_iff)
prefer 3 apply (simp add: LBV_eqns LBV_Lsubst1
                 disjoint_Un_iff disjoint_cons_iff)
prefer 2
apply (simp add: Lsubst_lemma2)
prefer 2
apply (rule_tac [2] LAlpha_LsubstI)
apply (erule_tac [2] asm_rl
       | rule_tac [2] LAlpha_LsubstI LFreeForIn_name_change
       | erule_tac [2] disjoint_LBV_LFV_imp_LFreeForIn)+

apply (drule_tac [3] bspec [THEN mp], erule_tac [3] LBeta1_type2,
       erule_tac [3] asm_rl)
apply (drule_tac [2] bspec [THEN mp], erule_tac [2] LBeta1_type2,
       erule_tac [2] asm_rl)
apply (drule_tac [1] bspec [THEN mp], erule_tac [1] LBeta1_type2,
       erule_tac [1] asm_rl)
apply safe
apply (frule_tac N="M'" in LAlphaD1 [THEN LSkeltonEqD2])
apply (frule_tac N="N'a" in LAlphaD1 [THEN LSkeltonEqD2])
apply (frule_tac M="N'" in LAlphaD1 [THEN LSkeltonEqD1])
apply (rule_tac F="X Un LBV(M') Un LBV(N'a) Un LFV(M') Un LFV(N'a)"
        in infv [THEN InfiniteE])
apply (assumption | rule Fin_UnI prem1 LFV_Fin LBV_Fin)+
apply simp
apply (erule conjE)+
apply (subgoal_tac "LFreeForIn(LVar(xa), x, M')"
         "LFreeForIn(LVar(xa), x, N'a)")
apply (rule_tac [3] disjoint_LBV_LFV_imp_LFreeForIn)
apply (rule_tac [2] disjoint_LBV_LFV_imp_LFreeForIn)
prefer 2 apply (simp add: disjoint_Un_iff2 disjoint_cons_iff2)
prefer 5 apply (simp add: disjoint_Un_iff2 disjoint_cons_iff2)
apply (erule_tac [2] asm_rl | rule_tac [2] LTerm.intros)+
apply (rule conjI [THEN exI])
apply (rule_tac [2] exI)
apply (assumption | rule LAlpha_LLamI3 conjI)+
apply (case_tac "x: LFV(M')")
apply (simp add: LBV_eqns LBV_Lsubst1
         disjoint_Un_iff disjoint_cons_iff)
apply (simp add: LBV_eqns
         disjoint_Un_iff disjoint_cons_iff)
apply (assumption | rule LBeta1_LLamI LBeta1_LsubstI)+

apply (rule_tac M1="N" and X1="X" in 
         infv [THEN Infinite_LVariable_LAlpha_lemma3, THEN revcut_rl])
apply (assumption | rule prem1)+
apply (erule exE)
apply (erule conjE)
apply (rule conjI [THEN exI])
apply (rule_tac [2] exI)
apply (assumption | rule LAlpha_LAppI conjI)+
apply (simp add: LAlphaD1 [THEN LSkeltonEqD2]
           disjoint_Un_iff LBV_eqns)
apply (assumption | rule LBeta1_LAppI1)+
apply (erule LAlphaD1 [THEN LSkeltonEqD2])

apply (rule_tac M1="M" and X1="X" in 
         infv [THEN Infinite_LVariable_LAlpha_lemma3, THEN revcut_rl])
apply (assumption | rule prem1)+
apply (erule exE)
apply (erule conjE)
apply (rule conjI [THEN exI])
apply (rule_tac [2] exI)
apply (assumption | rule LAlpha_LAppI conjI)+
apply (simp add: LAlphaD1 [THEN LSkeltonEqD2]
           disjoint_Un_iff LBV_eqns)
apply (assumption | rule LBeta1_LAppI2)+
apply (erule LAlphaD1 [THEN LSkeltonEqD2])
done

lemma LBeta1_LAlpha_parallel:
  assumes infv: "Infinite(LVariable)"
  and major: "LBeta1(M, N)"
  and prem1: "x: LVariable"
  and prem2: "X: LTerm"
  shows "EX M' N'. LAlpha(M, M') & LAlpha(N, N') &
            LFreeForIn(X, x, M') & LFreeForIn(X, x, N') & LBeta1(M', N')"
apply (rule_tac X1="LFV(X)" in LBeta1_LAlpha_parallel_lemma
        [OF infv major, THEN revcut_rl])
apply (rule prem2 [THEN LFV_Fin])
apply (elim exE conjE)
apply (assumption | rule exI conjI)+
apply (assumption | rule disjoint_LBV_LFV_imp_LFreeForIn
         prem1 prem2 conjI disjoint_subset
         LBeta1_LBV_lemma subset_refl
       | erule LAlphaD1 [THEN LSkeltonEqD2])+
done

end
