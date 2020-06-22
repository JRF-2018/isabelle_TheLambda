(*
    File:        Lambda.thy
    Time-stamp:  <2016-01-03T14:03:42Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory Lambda imports LBeta begin

axiomatization where
  Infinite_LVariable: "Infinite(LVariable)"

definition LAQ :: "i=>i" where
"LAQ(M) == {N: LTerm. LAlpha(M, N)}"

definition Term :: "i" where
"Term == {LAQ(M). M: LTerm}"

definition Var :: "i=>i" where
"Var(x) == {LVar(x)}"

definition Lam :: "[i,i]=>i" where
"Lam(x, M) == {m': LTerm. M: Term & (EX m: M. LAlpha(m', LLam(x, m)))}"

definition App :: "[i,i]=>i" where
"App(M, N) == {m: LTerm. M: Term & N: Term &
                       (EX a b. a: M & b: N & m = LApp(a, b))}"

definition FV :: "i=>i" where
"FV(M) == INT m: M. LFV(m)"

definition subst :: "[i,i,i]=>i" where
"subst(M, x, N) == {m': LTerm. EX m n. m: M & n: N & 
                     LFreeForIn(n, x, m) &
                     LAlpha(Lsubst(m, x, n), m')}"

definition Beta1 :: "[i,i]=>o" where
"Beta1(M, N) == M: Term & N: Term & (EX m: M. EX n: N. LBeta1(m, n))"


lemmas LAlpha_LLamE2 = Infinite_LVariable [THEN LAlpha_LLamE]
lemmas LAlpha_LTermEs2 = LAlpha_LVarE LAlpha_LLamE2
                         LAlpha_LAppE


 (** LAQ: LAlpha-quotient **)
lemma LAQ_I:
  "LAlpha(M, N) ==> N: LAQ(M)"
apply (unfold LAQ_def)
apply (blast dest: LAlphaD1 [THEN LSkeltonEqD2])
done

lemma LAQ_D:
  "N: LAQ(M) ==> LAlpha(M, N)"
apply (unfold LAQ_def)
apply blast
done

lemma LAQ_self:
  "M: LTerm ==> M: LAQ(M)"
apply (rule LAQ_I)
apply (erule LAlpha_refl)
done

lemma LAQ_eqI:
  "LAlpha(M, N) ==> LAQ(M) = LAQ(N)"
apply (rule equalityI)
apply (safe dest!: LAQ_D intro!: LAQ_I)
apply (erule LAlpha_sym [THEN LAlpha_trans])
apply assumption
apply (erule LAlpha_trans)
apply assumption
done

lemma LAQ_eqD:
  "[| LAQ(M) = LAQ(N); M: LTerm |] ==> LAlpha(M, N)"
apply (erule equalityE)
apply (drule subsetD, erule LAQ_self)
apply (erule LAQ_D [THEN LAlpha_sym])
done


(** Term **)
lemma TermI:
  "[| m: LTerm; M = LAQ(m) |] ==> M: Term"
apply (unfold Term_def)
apply blast
done

lemma LAQ_type:
  "m: LTerm ==> LAQ(m): Term"
apply (assumption | rule TermI refl)+
done

lemma TermE:
  "[| M: Term;
      !! m. [| M = LAQ(m); m: LTerm |] ==> R
   |] ==> R"
apply (unfold Term_def)
apply blast
done

lemma Term_LFreeForInE:
  assumes major: "M: Term"
  and prem1: "x: LVariable"
  and prem2: "n: LTerm"
  and prem3: "!!m. [| M = LAQ(m); m: LTerm; LFreeForIn(n, x, m) |] ==> R"
  shows "R"
apply (rule major [THEN TermE])
apply (rule Infinite_LVariable [THEN Infinite_LVariable_LAlpha_lemma,
         THEN bexE])
apply (rule_tac [2] prem1)
apply (rule_tac [2] prem2)
apply assumption
apply (rule prem3)
apply (safe dest!: LAQ_eqI)
apply assumption+
done

lemma Term_LFreeForInE2:
  assumes major: "M: Term"
  and prem1: "x: LVariable"
  and prem2: "X: Fin(LTerm)"
  and prem3:
     "!!m. [| M = LAQ(m); m: LTerm; ALL n: X. LFreeForIn(n, x, m) |]
            ==> R"
  shows "R"
apply (rule major [THEN TermE])
apply (rule Infinite_LVariable [THEN Infinite_LVariable_LAlpha_lemma2,
         THEN bexE])
apply (rule_tac [2] prem1)
apply (rule_tac [2] prem2)
apply assumption
apply (rule prem3)
apply (safe dest!: LAQ_eqI)
apply (erule_tac [3] bspec)
apply assumption+
done

lemma LAQ_LVar:
  "x: LVariable ==> LAQ(LVar(x)) = Var(x)"
apply (unfold Var_def)
apply (blast intro: LAlpha_LVarI dest!: LAQ_D intro!: LAQ_I
         elim!: LAlpha_LTermEs2)
done

lemma LAQ_LLam:
  "[| x: LVariable; m: LTerm |] ==> LAQ(LLam(x, m)) = Lam(x, LAQ(m))"
apply (unfold Lam_def)
apply (rule equalityI)
apply (safe dest!: LAQ_D intro!: LAQ_type LAQ_I 
         elim!: TermE LAlpha_LTermEs2)
apply (erule LAlphaD1 [THEN LSkeltonEqD2])
apply (erule_tac [3] LAlphaD1 [THEN LSkeltonEqD1])
apply (drule_tac [2] LFreeForInD1)
apply (erule_tac [2] LTerm_typeEs)
prefer 2 apply assumption
apply (rule bexI)
apply (assumption | rule LAQ_self LAlpha_sym [THEN LAlpha_LLamI1])+
apply (drule LAlpha_LLamI2)
apply (rule_tac [3] bexI)
apply (assumption | rule LAQ_I)+
apply (rule LAlpha_trans)
apply (erule_tac [2] LAlpha_sym)
apply (erule LAlpha_LLamI1)
apply assumption
done

lemma LAQ_LApp:
  "[| m: LTerm; n: LTerm |] ==> LAQ(LApp(m, n)) = App(LAQ(m), LAQ(n))"
apply (unfold App_def)
apply (blast dest!: LAQ_D intro: LAlpha_LTermIs elim!: TermE
         intro: LAlphaD1 [THEN LSkeltonEqD1]
                LAlphaD1 [THEN LSkeltonEqD2]
         intro!: LAQ_I LAQ_type elim!: LAlpha_LTermEs2)
done

lemmas Term_LAQ_sym = LAQ_LVar LAQ_LLam LAQ_LApp
lemmas Term_LAQ = Term_LAQ_sym [THEN sym]

lemma Term_VarI:
  assumes major: "x: LVariable"
  shows "Var(x): Term"
apply (rule major [THEN LAQ_LVar, THEN subst])
apply (rule TermI)
apply (rule_tac [2] refl)
apply (assumption | rule LTerm.intros major)+
done

lemma Term_LamI:
  assumes prem1: "x: LVariable"
  and prem2: "M: Term"
  shows "Lam(x, M): Term"
apply (rule prem2 [THEN TermE])
apply hypsubst
apply (rule prem1 [THEN LAQ_LLam, THEN subst])
apply assumption
apply (rule TermI)
apply (rule_tac [2] refl)
apply (assumption | rule prem1 LTerm.intros)+
done

lemma Term_AppI:
  assumes prem1: "M: Term"
  and prem2: "N: Term"
  shows "App(M, N): Term"
apply (rule prem1 [THEN TermE])
apply (rule prem2 [THEN TermE])
apply hypsubst
apply (rule LAQ_LApp [THEN subst])
apply (rule_tac [3] TermI)
apply (rule_tac [4] refl)
apply (assumption | rule LTerm.intros)+
done

lemmas Term_intros = Term_VarI Term_LamI Term_AppI

lemma Term_VarD:
  "Var(x): Term ==> x: LVariable"
apply (unfold Var_def)
apply (erule TermE)
apply (drule equalityD1)
apply (drule singletonI [THEN [2] subsetD])
apply (drule LAQ_D)
apply (erule LAlpha_sym [THEN LAlpha_LVarE])
apply assumption
done

lemma Term_LamE:
  assumes major: "Lam(x, M): Term"
  and prem: "[| x: LVariable; M: Term |] ==> R"
  shows "R"
apply (rule major [unfolded Lam_def, THEN TermE])
apply (rule prem)
apply (drule_tac [2] equalityD2)
apply (drule_tac [2] LAQ_self [THEN [2] subsetD])
apply (drule equalityD2)
apply (drule_tac LAQ_self [THEN [2] subsetD])
apply safe
apply (drule LAlphaD1 [THEN LSkeltonEqD2])
apply (erule LTerm_typeEs)
apply assumption
done

lemma Term_AppE:
  assumes major: "App(M, N): Term"
  and prem: "[| M: Term; N: Term |] ==> R"
  shows "R"
apply (rule major [unfolded App_def, THEN TermE])
apply (drule equalityD2)
apply (drule LAQ_self [THEN [2] subsetD])
apply (rule_tac [2] prem)
apply safe
done

lemmas Term_typeEs = Term_VarD [elim_format] Term_LamE Term_AppE

lemma Term_cases:
  assumes major: "M: Term"
  and prem1:
      "!! x. [| x: LVariable; M = Var(x) |] ==> R"
  and prem2:
      "!! x N. [| x: LVariable; N: Term; M = Lam(x, N) |] ==> R"
  and prem3:
      "!! A B. [| A: Term; B: Term; M = App(A, B) |] ==> R"
  shows "R"
apply (rule major [THEN TermE])
apply (erule LTerm.cases)
apply (rule_tac [3] prem3)
apply (rule_tac [2] prem2)
apply (rule_tac [1] prem1)
prefer 8
apply hypsubst
apply (rule Term_LAQ_sym)
prefer 7
apply hypsubst
apply (rule Term_LAQ_sym)
prefer 6
apply hypsubst
apply (rule Term_LAQ_sym)
apply (assumption | rule LAQ_type)+
done

lemma Term_induct:
  assumes major: "M: Term"
  and "!! x. x: LVariable ==> P(Var(x))"
  and "!! x N. [| x: LVariable; N: Term; P(N) |] ==> P(Lam(x, N))"
  and "!! A B. [| A: Term; P(A); B: Term; P(B) |] ==> P(App(A, B))"
  shows "P(M)"
apply (rule major [THEN TermE])
apply (erule rev_mp)
apply (rule_tac x="M" in spec)
apply (erule LTerm.induct)
apply safe
apply (simp_all add: Term_LAQ_sym)
apply (assumption | rule LAQ_type assms)+
done


(** FV **)
lemma FV_LAQ:
  assumes major: "m: LTerm"
  shows "FV(LAQ(m)) = LFV(m)"
apply (unfold FV_def)
apply (rule equalityI)
apply (safe elim!: LFV_E LAQ_D [elim_format] intro!: LAQ_I)
apply (drule_tac [3] equals0D)
apply (erule_tac [3] notE)
apply (rule_tac [3] RepFunI)
apply (rule_tac [3] major [THEN LAQ_self])
apply (rule_tac [2] LFV_I)
apply (erule_tac [2] LAlphaD2)
apply (erule_tac [2] asm_rl)
apply (erule INT_E)
apply (rule major [THEN LAQ_self])
done

lemma FV_Var:
  "x: LVariable ==> FV(Var(x)) = {x}"
apply (simp add: Term_LAQ FV_LAQ)
done

lemma FV_Lam:
  assumes prem1: "x: LVariable"
  and prem2: "M: Term"
  shows "FV(Lam(x, M)) = FV(M) - {x}"
apply (rule prem2 [THEN TermE])
apply (insert prem1)
apply (simp add: Term_LAQ FV_LAQ)
done

lemma FV_App:
  assumes prem1: "M: Term"
  and prem2: "N: Term"
  shows "FV(App(M, N)) = FV(M) Un FV(N)"
apply (rule prem1 [THEN TermE])
apply (rule prem2 [THEN TermE])
apply (simp add: Term_LAQ FV_LAQ)
done

lemmas FV_eqns = FV_Var FV_App FV_Lam


(** subst **)
lemma subst_LAQ:
  assumes major: "LFreeForIn(n, x, m)"
  shows "subst(LAQ(m), x, LAQ(n)) = LAQ(Lsubst(m, x, n))"
apply (unfold subst_def)
apply (insert major [THEN LFreeForInD1] major [THEN LFreeForInD2]
              major [THEN LFreeForInD3])
apply (insert major)
apply (rule equalityI)
apply (safe elim!: LAlpha_LTermEs2 LTerm.free_elims
         dest!: LAQ_D intro!: LAQ_I)
apply (rule LAlpha_trans)
prefer 2 apply assumption
apply (assumption | rule LAlpha_LsubstI)+
apply (erule LAlphaD1 [THEN LSkeltonEqD2])
apply (assumption | rule exI LAQ_self conjI)+
done

lemma subst_type:
  assumes prem1: "M: Term"
  and prem2: "x: LVariable"
  and prem3: "N: Term"
  shows "subst(M, x, N): Term"
apply (rule prem3 [THEN TermE])
apply (rule Term_LFreeForInE [OF prem1 prem2])
apply assumption
apply (simp add: subst_LAQ)
apply (assumption | rule LAQ_type Lsubst_type prem2)+
done

lemma subst_Var1:
  assumes prem1: "x: LVariable"
  and prem2: "N: Term"
  shows "subst(Var(x), x, N) = N"
apply (insert prem1)
apply (rule prem2 [THEN TermE])
apply (simp add: Term_LAQ)
apply (rule subst_LAQ [THEN trans])
apply (assumption | rule LFreeForIn_LTermIs)+
apply simp
done

lemma subst_Var2:
  assumes prem1: "x ~= y"
  and prem2: "y: LVariable"
  and prem3: "x: LVariable"
  and prem4: "N: Term"
  shows "subst(Var(y), x, N) = Var(y)"
apply (insert prem1 prem2 prem3)
apply (rule prem4 [THEN TermE])
apply (simp add: Term_LAQ)
apply (rule subst_LAQ [THEN trans])
apply (assumption | rule LFreeForIn_LTermIs)+
apply simp
done

lemma subst_Lam1:
  assumes prem1: "x: LVariable"
  and prem2: "M: Term"
  and prem3: "N: Term"
  shows "subst(Lam(x, M), x, N) = Lam(x, M)"
apply (rule prem3 [THEN TermE])
apply (rule prem2 [THEN TermE])
apply (insert prem1)
apply (simp add: Term_LAQ)
apply (rule subst_LAQ [THEN trans])
apply (rule LFreeForIn_LLamI1)
prefer 4 apply simp
apply assumption+
done

lemma subst_Lam2:
  assumes prem0: "x: LVariable"
  and prem1: "y: LVariable"
  and prem2: "M: Term"
  and prem3: "N: Term"
  and prem4: "y ~= x"
  and prem5: "x ~: FV(N)"
  shows "subst(Lam(x, M), y, N) = Lam(x, subst(M, y, N))"
apply (rule prem3 [THEN TermE])
apply (rule Term_LFreeForInE [OF prem2 prem1])
apply assumption
apply (insert prem0 prem1 prem4 prem5)
apply (simp add: Term_LAQ subst_LAQ FV_LAQ)
apply (rule subst_LAQ [THEN trans])
prefer 2 apply simp
apply (rule LFreeForIn_LLamI2)
prefer 3 apply blast
apply assumption+
done

lemma subst_App:
  assumes prem1: "A: Term"
  and prem2: "B: Term"
  and prem3: "x: LVariable"
  and prem4: "N: Term"
  shows "subst(App(A, B), x, N) = App(subst(A, x, N), subst(B, x, N))"
apply (rule prem4 [THEN TermE])
apply (rule Term_LFreeForInE [OF prem1 prem3])
apply assumption
apply (rule Term_LFreeForInE [OF prem2 prem3])
apply assumption
apply (simp add: Term_LAQ LFreeForIn_LAppI subst_LAQ)
done

lemma subst_self:
  assumes prem1: "M: Term"
  and prem2: "x: LVariable"
  shows "subst(M, x, Var(x)) = M"
apply (rule_tac n="LVar(x)" in Term_LFreeForInE [OF prem1 prem2])
apply (rule LTerm.intros prem2)+
apply (insert prem2)
apply (simp add: Term_LAQ subst_LAQ Lsubst_self)
done

lemma subst_lemma2:
  assumes prem1: "M: Term"
  and prem2: "N: Term"
  and prem3: "x: LVariable"
  and prem4: "y: LVariable"
  and prem5: "y ~: FV(M)"
  shows "subst(subst(M, x, Var(y)), y, N) = subst(M, x, N)"
apply (rule prem2 [THEN TermE])
apply (rule_tac X="{LVar(y), m}" in Term_LFreeForInE2 [OF prem1 prem3])
apply (assumption | rule prem4 LTerm.intros Fin.intros)+
apply (insert prem3 prem4 prem5)
apply (simp add: Term_LAQ subst_LAQ FV_LAQ)
apply (erule conjE)
apply (rule subst_LAQ [THEN trans])
apply (assumption | rule LFreeForIn_name_change)+
apply (simp add: Lsubst_lemma2)
done

lemmas subst_eqns = subst_Var1 subst_Var2 subst_App subst_Lam1 
                  subst_Lam2 subst_self subst_lemma2


(** Term.free_iffs **)
lemma Var_iff:
  "Var(x) = Var(y) <-> x = y"
apply (unfold Var_def)
apply (simp only: singleton_iff2)
apply (blast elim!: LTerm.free_elims)
done

lemma App_eqD:
  assumes major: "App(A, B) = App(A', B')"
  and prem1: "A: Term"
  and prem2: "B: Term"
  shows "A = A' & B = B'"
apply (insert prem1 prem2)
apply (subgoal_tac "App(A', B'): Term")
apply (rule_tac [2] major [THEN subst])
apply (erule_tac [2] asm_rl | rule_tac [2] Term_intros)+
apply (erule Term_AppE)
apply (erule TermE)+
apply (insert major)
apply hypsubst
apply (simp only: Term_LAQ)
apply (drule LAQ_eqD)
apply (safe elim!: LAlpha_LTermEs2 LTerm.free_elims)
apply (erule LAQ_eqI)+
done

lemma App_iff:
  "[| A: Term; B: Term |] ==>
       App(A, B) = App(A', B') <-> A = A' & B = B'"
apply (rule iffI)
apply (erule App_eqD)
apply assumption+
apply blast
done

lemma Lam_eqD:
  assumes major: "Lam(x, M) = Lam(y, M')"
  and prem1: "x: LVariable"
  and prem2: "M: Term"
  and prem3: "y: LVariable"
  and prem4: "M': Term"
  shows "M = subst(M', y, Var(x)) & x ~: FV(M') - {y}"
apply (rule prem2 [THEN TermE])
apply (rule_tac n="LVar(x)" in Term_LFreeForInE [OF prem4 prem3])
apply (rule prem1 LTerm.intros)+
apply (insert prem1 prem3 major)
apply (simp only: Term_LAQ subst_LAQ FV_LAQ)
apply (drule LAQ_eqD [THEN LAlpha_sym])
apply (safe elim!: LAlpha_LTermEs2 LTerm.free_elims)
apply (erule_tac [3] LFV_E)
apply (erule_tac [3] swap)
apply (drule_tac [3] LAlphaD2, erule_tac [3] asm_rl)
apply (erule_tac [3] LFV_I)
apply (rule_tac [2] LAQ_eqI)
apply (rule LAQ_eqI)
apply (simp add: Lsubst_self)
apply (erule LAlpha_sym)
apply (erule LAlpha_trans)
apply (rule LAlpha_LsubstI)
apply (erule LAlpha_sym)
apply (assumption | rule LAlpha_LVarI)+
done

lemma Alpha:
  assumes prem1: "M: Term"
  and prem2: "x: LVariable"
  and prem3: "y: LVariable"
  and prem4: "x ~: FV(M) - {y}"
  shows "Lam(y, M) = Lam(x, subst(M, y, Var(x)))"
apply (rule_tac n="LVar(x)" in Term_LFreeForInE [OF prem1 prem3])
apply (rule prem2 LTerm.intros)+
apply (insert prem2 prem3 prem4)
apply (simp add: Term_LAQ subst_LAQ FV_LAQ)
apply (rule LAQ_eqI)
apply (erule disjE)
prefer 2
apply hypsubst
apply (simp add: Lsubst_self)
apply (rule_tac [2] LAlpha_LLamI3)
apply (assumption | rule LAlpha_refl LTerm.intros)+
done

lemma Lam_iff:
  "[| M: Term; N: Term; x: LVariable; y: LVariable |] ==>
     Lam(x, M) = Lam(y, N) <-> M = subst(N, y, Var(x)) & x ~: FV(N) - {y}"
apply (rule iffI)
apply (erule Lam_eqD)
apply assumption+
apply (erule conjE)
apply hypsubst
apply (rule Alpha [THEN sym]) 
apply assumption+
done

lemma Var_Lam_free_iff:
  "x: LVariable ==> Var(x) = Lam(y, M) <-> False"
apply safe
apply (subgoal_tac "Lam(y, M): Term")
apply (erule_tac [2] subst)
apply (erule_tac [2] asm_rl | rule_tac [2] Term_intros)+
apply (erule Term_typeEs)
apply (erule TermE)+
apply (rotate_tac 2)
apply (simp only: Term_LAQ)
apply (drule LAQ_eqD)
apply (safe elim!: LTerm.free_elims LAlpha_LTermEs2)
done

lemma Var_App_free_iff:
  "x: LVariable ==> Var(x) = App(M, N) <-> False"
apply safe
apply (subgoal_tac "App(M, N): Term")
apply (erule_tac [2] subst)
apply (erule_tac [2] asm_rl | rule_tac [2] Term_intros)+
apply (erule Term_typeEs)
apply (erule TermE)+
apply (rotate_tac 2)
apply (simp only: Term_LAQ)
apply (drule LAQ_eqD)
apply (safe elim!: LTerm.free_elims LAlpha_LTermEs2)
done

lemma Lam_Var_free_iff:
  "[| x: LVariable; M: Term |] ==> Lam(x, M) = Var(y) <-> False"
apply safe
apply (subgoal_tac "Var(y): Term")
apply (erule_tac [2] subst)
apply (erule_tac [2] asm_rl | rule_tac [2] Term_intros)+
apply (erule Term_typeEs)
apply (erule TermE)+
apply (rotate_tac 2)
apply (simp only: Term_LAQ)
apply (drule LAQ_eqD)
apply (safe elim!: LTerm.free_elims LAlpha_LTermEs2)
done

lemma Lam_App_free_iff:
  "[| x: LVariable; M: Term |] ==> Lam(x, M) = App(A, B) <-> False"
apply safe
apply (subgoal_tac "App(A, B): Term")
apply (erule_tac [2] subst)
apply (erule_tac [2] asm_rl | rule_tac [2] Term_intros)+
apply (erule Term_typeEs)
apply (erule TermE)+
apply (rotate_tac 2)
apply (simp only: Term_LAQ)
apply (drule LAQ_eqD)
apply (safe elim!: LTerm.free_elims LAlpha_LTermEs2)
done

lemma App_Var_free_iff:
  "[| M: Term; N: Term |] ==> App(M, N) = Var(y) <-> False"
apply safe
apply (subgoal_tac "Var(y): Term")
apply (erule_tac [2] subst)
apply (erule_tac [2] asm_rl | rule_tac [2] Term_intros)+
apply (erule Term_typeEs)
apply (erule TermE)+
apply (rotate_tac 2)
apply (simp only: Term_LAQ)
apply (drule LAQ_eqD)
apply (safe elim!: LTerm.free_elims LAlpha_LTermEs2)
done

lemma App_Lam_free_iff:
  "[| A: Term; B: Term |] ==> App(A, B) = Lam(x, M) <-> False"
apply safe
apply (subgoal_tac "Lam(x, M): Term")
apply (erule_tac [2] subst)
apply (erule_tac [2] asm_rl | rule_tac [2] Term_intros)+
apply (erule Term_typeEs)
apply (erule TermE)+
apply (rotate_tac 2)
apply (simp only: Term_LAQ)
apply (drule LAQ_eqD)
apply (safe elim!: LTerm.free_elims LAlpha_LTermEs2)
done

lemmas Term_free_iffs = Var_iff App_iff Lam_iff
  Var_Lam_free_iff Var_App_free_iff
  Lam_Var_free_iff Lam_App_free_iff
  App_Var_free_iff App_Lam_free_iff


(** Beta1 **)
lemma Beta1D1:
  "Beta1(M, N) ==> M: Term"
apply (unfold Beta1_def)
apply (erule conjunct1)
done

lemma Beta1D2:
  "Beta1(M, N) ==> N: Term"
apply (unfold Beta1_def)
apply (erule conjunct2 [THEN conjunct1])
done

lemma Beta1_baseI:
  assumes prem1: "M: Term"
  and prem2: "x: LVariable"
  and prem3: "N: Term"
  shows "Beta1(App(Lam(x, M), N), subst(M, x, N))"
apply (unfold Beta1_def)
apply (assumption | rule Term_intros prem1 prem2 prem3 conjI subst_type)+
apply (rule prem3 [THEN TermE])
apply (rule Term_LFreeForInE [OF prem1 prem2])
apply assumption
apply (insert prem2)
apply (simp add: Term_LAQ subst_LAQ)
apply (assumption | rule LTerm.intros bexI LBeta1_baseI
        LAQ_self Lsubst_type)+
done

lemma Beta1_LamI:
  "[| Beta1(M, M'); x: LVariable |]  ==>
        Beta1(Lam(x, M), Lam(x, M'))"
apply (unfold Beta1_def)
apply (safe intro!: Term_intros)
apply (erule TermE)+
apply hypsubst
apply (simp add: Term_LAQ)
apply (drule LAQ_D)+
apply (rule bexI)
apply (rule bexI)
apply (rule LBeta1_LLamI)
apply (assumption | rule LAQ_I LAlpha_LLamI1)+
done

lemma Beta1_AppI1:
  "[| Beta1(M, M'); N: Term |]  ==>
        Beta1(App(M, N), App(M', N))"
apply (unfold Beta1_def)
apply (safe intro!: Term_intros)
apply (erule TermE)+
apply hypsubst
apply (simp add: Term_LAQ)
apply (drule LAQ_D)+
apply (rule bexI)
apply (rule bexI)
apply (rule LBeta1_LAppI1)
apply (assumption | rule LAQ_I LAlpha_LAppI LAlpha_refl)+
done

lemma Beta1_AppI2:
  "[| Beta1(N, N'); M: Term |]  ==>
        Beta1(App(M, N), App(M, N'))"
apply (unfold Beta1_def)
apply (safe intro!: Term_intros)
apply (erule TermE)+
apply hypsubst
apply (simp add: Term_LAQ)
apply (drule LAQ_D)+
apply (rule bexI)
apply (rule bexI)
apply (rule LBeta1_LAppI2)
apply (assumption | rule LAQ_I LAlpha_LAppI LAlpha_refl)+
done

lemma Beta1_VarE:
  "Beta1(Var(x), N) ==> R"
apply (unfold Beta1_def)
apply (safe elim!: Term_typeEs)
apply (rotate_tac 2)
apply (simp only: Term_LAQ)
apply (safe dest!: LAQ_D elim!: LAlpha_LTermEs2 LBeta1_LTermEs)
done

lemma Beta1_LamE1:
  assumes major: "Beta1(Lam(x, M), N)"
  and prem1:
     "!!N'. [| x: LVariable; N = Lam(x, N'); Beta1(M, N')|]
         ==> R"
  and prem2:
     "!!y N'. [| x: LVariable; y: LVariable; M: Term; N': Term; y ~: FV(M);
          N = Lam(y, N'); Beta1(subst(M, x, Var(y)), N')|]
         ==> R"
  shows "R"
apply (insert major)
apply (unfold Beta1_def)
apply (erule Term_typeEs conjE bexE TermE)+
apply (rotate_tac 3)
apply (simp only: Term_LAQ)
apply (drule LAQ_D)+
apply (erule LAlpha_LTermEs2)
apply hypsubst
apply (erule_tac LBeta1_LTermEs)
apply hypsubst
prefer 2
apply hypsubst
apply (erule_tac LBeta1_LTermEs)
apply hypsubst
prefer 2
apply (rule_tac [2] y="y" and N'="LAQ(N'a)" in prem2)
apply (rule_tac N'="LAQ(N'a)" in prem1)
apply (unfold Beta1_def)
apply (safe intro!: subst_type LAQ_type Term_intros)
prefer 2
prefer 4
prefer 7
apply (erule LBeta1_type2)+
apply (drule_tac [5] M="ma" in LAQ_eqI)
apply (simp_all add: Term_LAQ FV_LAQ LBeta1_type2 subst_LAQ)
apply (erule LAQ_eqI)
apply (erule_tac [3] LAQ_eqI)
apply (erule_tac [2] LFV_E)
apply (drule_tac [2] LAlphaD2, erule_tac [2] asm_rl)
apply (erule_tac [2] notE, erule_tac [2] LFV_I)
apply (assumption | rule bexI LAQ_self LAQ_I
       | erule LBeta1_type2 | erule LAlpha_sym)+
done

lemma Beta1_AppE1:
  assumes major: "Beta1(App(A, B), N)"
  and prem1:
     "!!x N'. [| x: LVariable; N': Term; B: Term;
         A = Lam(x, N'); N = subst(N', x, B) |] ==> R"
  and prem2:
     "!!A'. [| N = App(A',B); Beta1(A, A'); B: Term |] ==> R"
  and prem3:
     "!!B'. [| N = App(A, B'); Beta1(B, B'); A: Term |] ==> R"
  shows "R"
apply (insert major)
apply (unfold Beta1_def)
apply (erule Term_typeEs conjE bexE TermE)+
apply (rotate_tac 3)
apply (simp only: Term_LAQ)
apply (drule LAQ_D)+
apply (erule_tac LAlpha_LTermEs2)
apply hypsubst
apply (erule_tac LBeta1_LTermEs)
prefer 3
apply hypsubst
apply (drule LAQ_eqI)+
prefer 3
apply hypsubst
apply (drule LAQ_eqI)+
prefer 3
apply hypsubst
apply (drule LAQ_eqI)+
apply (rule_tac [3] B'="LAQ(B')" in prem3)
apply (rule_tac [2] A'="LAQ(A')" in prem2)
apply (rule_tac x="x" and N'="LAQ(N')" in prem1)
apply (unfold Beta1_def)
apply (safe intro!: subst_type LAQ_type Term_intros)
prefer 6
prefer 9
apply (erule LBeta1_type2)+
apply (erule LFreeForInD2)
apply (erule LFreeForInD3)
apply (simp_all add: Term_LAQ FV_LAQ LBeta1_type2
         LFreeForInD2 LFreeForInD3 subst_LAQ)
apply (assumption | rule bexI LAQ_self LAQ_I
       | erule LBeta1_type2 LBeta1_type1 LAlpha_sym)+
done

lemma Beta1_substI:
  assumes major: "Beta1(M, M')"
  and prem1: "x: LVariable"
  and prem2: "N: Term"
  shows "Beta1(subst(M, x, N), subst(M', x, N))"
apply (unfold Beta1_def)
apply (rule prem2 [THEN TermE])
apply (rule Term_LFreeForInE [OF
        major [unfolded Beta1_def, THEN conjunct1] prem1])
apply assumption
apply (rule_tac n="m" in Term_LFreeForInE [OF
        major [unfolded Beta1_def, THEN conjunct2, THEN conjunct1] prem1])
apply assumption
apply (insert major [unfolded Beta1_def, THEN conjunct2, THEN conjunct2])
apply (erule bexE)+
apply (simp only: subst_LAQ)
apply (assumption | rule LAQ_type Lsubst_type conjI)+
apply (drule_tac X="m" in
        Infinite_LVariable [THEN LBeta1_LAlpha_parallel])
apply (erule LFreeForInD2)
apply assumption
apply (safe dest!: LAQ_D)
apply (rule bexI [THEN bexI])
apply (erule LBeta1_LsubstI)
apply assumption+
apply (assumption | rule LAQ_I LAlpha_LsubstI LAlpha_refl
       | erule LAlpha_trans)+
done

lemma Beta1_FV_lemma:
  assumes major: "Beta1(M, N)"
  shows "FV(N) <= FV(M)"
apply (rule major [unfolded Beta1_def, THEN conjunct1, THEN TermE])
apply (rule major [unfolded Beta1_def, THEN conjunct2, 
                   THEN conjunct1, THEN TermE])
apply (insert major)
apply (unfold Beta1_def)
apply (erule bexE conjE)+
apply hypsubst
apply (drule LAQ_D [THEN LAQ_eqI])+
apply (simp only: FV_LAQ LBeta1_type1 LBeta1_type2)
apply (erule LBeta1_LFV_lemma)
done

lemma FV_subst_not_in_lemma:
  assumes prem1: "M: Term"
  and prem2: "x: LVariable"
  and prem3: "N: Term"
  shows "x ~: FV(subst(M, x, N)) - FV(N)"
apply (insert prem2)
apply (rule prem3 [THEN TermE])
apply (rule Term_LFreeForInE [OF prem1 prem2])
apply assumption
apply (simp add: FV_LAQ subst_LAQ)
apply (safe intro!: Lsubst_type elim!: LFV_E LFreeIn_LsubstE)
apply (erule notE, erule LFV_I)
done

lemma Beta1_LamE:
  assumes major: "Beta1(Lam(x, M), N)"
  and prem:
     "!!N'. [| x: LVariable; N = Lam(x, N'); Beta1(M, N')|]
         ==> R"
  shows "R"
apply (rule major [THEN Beta1_LamE1])
apply (frule_tac [2] Beta1_FV_lemma)
apply (rule_tac [2] M1="M" and x1="x" and N1="Var(y)" in
         FV_subst_not_in_lemma [THEN revcut_rl])
prefer 5
apply (simp add: FV_eqns)
defer 1
apply (erule_tac [5] disjE)
apply (drule_tac [5] x="y" and N="Var(x)" in Beta1_substI)
apply (erule_tac [2] asm_rl | rule_tac [2] Term_intros)+
apply (frule_tac [2] Term_VarI)
apply (rotate_tac [2] 9)
prefer 2
apply (simp add: subst_lemma2 subst_self)
prefer 2
apply (rotate_tac [3] 7)
prefer 3
apply (simp add: subst_self)
defer 1
apply (rule_tac [3] prem)
apply (rule_tac [2] prem)
apply (rule_tac [1] prem)
prefer 6
prefer 9
apply assumption+
apply safe
apply (rule Alpha)
prefer 4 apply blast
apply assumption+
done

lemma Fin_FV_I:
  "M: Term ==> FV(M): Fin(LVariable)"
apply (erule TermE)
apply hypsubst
apply (simp only: FV_LAQ)
apply (erule LFV_Fin)
done

lemma Infinite_LVariable_Alpha_lemma2:
  assumes major: "M: Term"
  and prem1: "x: LVariable"
  and prem2: "X: Fin(LVariable)"
  shows "EX y: LVariable. EX M': Term. Lam(x, M) = Lam(y, M') & y ~: X"
apply (rule_tac F="X Un FV(M)" in Infinite_LVariable [THEN InfiniteE])
apply (assumption | rule Fin_UnI Fin_FV_I prem2 major bexI conjI)+
apply (rule Alpha)
prefer 2 apply assumption
prefer 3 apply blast
prefer 3 apply blast
apply (assumption | rule major prem1 subst_type Term_intros)+
done

lemma Beta1_AppE:
  assumes major: "Beta1(App(A, B), N)"
  and prem1:
     "!!x N'. [| x: LVariable; N': Term; B: Term; x ~: FV(B);
         A = Lam(x, N'); N = subst(N', x, B) |] ==> R"
  and prem2:
     "!!A'. [| B: Term; Beta1(A, A'); N = App(A', B) |] ==> R"
  and prem3:
     "!!B'. [| A: Term; Beta1(B, B'); N = App(A, B') |] ==> R"
  shows "R"
apply (rule major [THEN Beta1_AppE1])
apply (rule_tac M1="N'" and X1="cons(x, FV(B))" in
         Infinite_LVariable_Alpha_lemma2 [THEN revcut_rl])
apply (assumption | rule Fin_FV_I Fin.intros)+
apply (erule Term_typeEs conjE bexE)+
apply (subgoal_tac "y ~= x")
prefer 2 apply blast
apply (erule swap, rule consI2)
apply (erule swap)
apply (erule swap)
apply (rotate_tac 7)
apply simp
apply (rule prem1)
prefer 5 apply assumption
apply assumption+
apply (rotate_tac 1)
apply (simp add: Term_free_iffs)
apply (elim conjE disjE)
apply (simp add: subst_lemma2)
apply (simp add: subst_lemma2)
apply (rule prem2)
apply (rule_tac [4] prem3)
apply assumption+
done

lemmas Beta1_TermEs = Beta1_VarE Beta1_LamE Beta1_AppE

end
