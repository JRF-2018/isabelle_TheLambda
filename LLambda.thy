(*
    File:        LLambda.thy
    Time-stamp:  <2020-06-22T04:31:28Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory LLambda imports LTermDef Poset InitSeg begin

definition LBinding :: "[i, i, i] => o" where
"LBinding(v, u, M) == M: LTerm & u: LOcc(M) & v: LOcc(M) &
       (EX x l m. u = <l, TLVar(x)> & v = <m, TLLam(x)> &
                   initseg(nat, m, l))"

definition LBoundBy :: "[i, i, i] => o" where
"LBoundBy(u, v, M) == EX x l m. u = <m, TLVar(x)> & v = <l, TLLam(x)> &
      greatest(initseg(nat), {n:list(nat). EX T. LBinding(<n, T>, u, M)}, l)"

definition LBoundIn :: "[i, i] => o" where
"LBoundIn(u, M) == M: LTerm & u: LOcc(M) & (EX l x. u = <l, TLVar(x)> &
      (EX v: LOcc(M). (EX m. v = <m, TLLam(x)> & initseg(nat, m, l))))"

definition LFreeIn :: "[i, i] => o" where
"LFreeIn(u, M) == M: LTerm & u: LOcc(M) & (EX l x. u = <l, TLVar(x)> &
       ~(EX v: LOcc(M). (EX m. v = <m, TLLam(x)> & initseg(nat, m, l))))"

definition LFV :: "i => i" where
"LFV(M) == {x: LVariable. EX l.  LFreeIn(<l, TLVar(x)> , M)}"

definition LFO :: "[i, i] => i" where
"LFO(x, M) == {u: list(nat)*LTag. EX l. u = <l, TLVar(x)> & LFreeIn(u, M)}"

definition Lsubst :: "[i, i, i] => i" where
"Lsubst(M, x, N) == Lgraft(M, domain(LFO(x, M)), N)"

definition LFreeForIn :: "[i, i, i]=>o" where
"LFreeForIn(N, x, M) == N: LTerm & x: LVariable & M: LTerm &
     (ALL z: LFV(N). ~ (EX l m.
        LFreeIn(<l, TLVar(x)>, M) &
        <m, TLLam(z)>: LOcc(M) & initseg(nat, m, l)))"

lemmas LOcc_domain = Occ_ind_cond_Occ_domain
    [OF LTerm_Occ_ind_cond]

lemmas LOcc_in_Occ_range = Occ_ind_cond_Occ_in_Occ_range
    [OF LTerm_Occ_ind_cond]

lemma LOcc_typeD1:
  assumes major: "<l, T>: LOcc(M)"
  and prem: "M: LTerm"
  shows "l: list(nat)"
apply (rule major [THEN prem [THEN LOcc_domain, THEN subsetD, THEN SigmaD1]])
done

lemma LOcc_typeD2:
  assumes major: "<l, T>: LOcc(M)"
  and prem: "M: LTerm"
  shows "T: LTag"
apply (rule major [THEN prem [THEN LOcc_domain, THEN subsetD, THEN SigmaD2]])
done

lemma LTerm_typeEs:
  "[| LVar(x): LTerm; x: LVariable ==> R |] ==> R"
  "[| LLam(x, M): LTerm; [| x: LVariable; M: LTerm |] ==> R |] ==> R"
  "[| LApp(M, N): LTerm; [| M: LTerm; N: LTerm |] ==> R |] ==> R"
apply (erule LTerm.cases)
apply simp_all
apply (erule LTerm.cases)
apply simp_all
apply (erule LTerm.cases)
apply simp_all
done

lemma LTag_typeEs:
  "[| TLVar(x): LTag; x: LVariable ==> R |] ==> R"
  "[| TLLam(x): LTag; x: LVariable ==> R |] ==> R"
apply (erule LTag.cases)
apply simp_all
apply (erule LTag.cases)
apply simp_all
done

lemma LOcc_LVarE:
  assumes major: "u: LOcc(LVar(x))"
  and prem: "u = <[], TLVar(x)> ==> R"
  shows "R"
apply (insert major)
apply (simp only: LOcc_eqns)
apply (erule Occ_consE)
apply (erule prem)
apply simp
done

lemma LOcc_LLamE:
  assumes major: "u: LOcc(LLam(x, M))"
  and prem1: "u = <[], TLLam(x)> ==> R"
  and prem2: "!! l T. [| u = <Cons(0, l), T>; <l, T>: LOcc(M) |] ==> R"
  shows "R"
apply (insert major)
apply (simp only: LOcc_eqns)
apply (erule Occ_consE)
apply (erule prem1)
apply simp
apply (erule succE)
apply (erule_tac [2] emptyE)
apply (rule prem2)
apply hypsubst
apply (rule refl)
apply simp
done

lemma LOcc_LAppE:
  assumes major: "u: LOcc(LApp(M, N))"
  and prem1: "u = <[], TLApp> ==> R"
  and prem2: "!! l T. [| u = <Cons(0, l), T>; <l, T>: LOcc(M) |] ==> R"
  and prem3: "!! l T. [| u = <Cons(1, l), T>; <l, T>: LOcc(N) |] ==> R"
  shows "R"
apply (insert major)
apply (simp only: LOcc_eqns)
apply (erule Occ_consE)
apply (erule prem1)
apply simp
apply (erule succE)
apply (erule_tac [2] succE)
apply (erule_tac [3] emptyE)
apply (rule_tac [2] prem2)
apply (rule prem3)
apply simp_all
done

lemmas LOcc_LTermEs = LOcc_LVarE LOcc_LLamE LOcc_LAppE

lemma LOcc_LTermIs:
  "<[], TLVar(x)>: LOcc(LVar(x))"
  "<[], TLLam(x)>: LOcc(LLam(x, M))"
  "<l, T>: LOcc(M) ==> <Cons(0, l), T>: LOcc(LLam(x, M))"
  "<[], TLApp>: LOcc(LApp(M, N))"
  "<l, T>: LOcc(M) ==> <Cons(0, l), T>: LOcc(LApp(M, N))"
  "<l, T>: LOcc(N) ==> <Cons(1, l), T>: LOcc(LApp(M, N))"
apply (simp_all add: LOcc_eqns)
apply (assumption | rule Occ_consI2 Occ_consI1 | simp)+
done

(** LBinding **)
lemma LBindingI:
  "[| M: LTerm; <l, TLLam(x)>: LOcc(M); <m, TLVar(x)>: LOcc(M);
      initseg(nat, l, m)
   |] ==> LBinding(<l, TLLam(x)>, <m, TLVar(x)>, M)"
apply (unfold LBinding_def)
apply blast
done

lemma LBindingE:
  "[| LBinding(v, u, M);
      !! x l m. [| v =  <l, TLLam(x)>; u = <m, TLVar(x)>; M: LTerm;
         <l, TLLam(x)>: LOcc(M); <m, TLVar(x)>: LOcc(M);
         initseg(nat, l, m) |] ==> R
   |] ==> R"
apply (unfold LBinding_def)
apply blast
done

lemma LBindingE2:
  "[| LBinding(<l, TLLam(x)>, <m, TLVar(x)>, M);
      [| M: LTerm;
         <l, TLLam(x)>: LOcc(M); <m, TLVar(x)>: LOcc(M);
         initseg(nat, l, m) |] ==> R
   |] ==> R"
apply (erule LBindingE)
apply simp
done

lemma LBindingD1:
  "LBinding(v, u, M) ==> M: LTerm"
apply (unfold LBinding_def)
apply (erule conjunct1)
done

lemma LBinding_LVarE:
  "LBinding(v, u, LVar(x)) ==> R"
apply (erule LBindingE)
apply (elim LOcc_LVarE)
apply simp
done

lemma LBinding_LLamE:
  assumes major: "LBinding(v, u, LLam(x, N))"
  and prem1: 
    "!!l m. [| x: LVariable; N: LTerm;
          v = <[], TLLam(x)>; u = <Cons(0, m), TLVar(x)>;
         <m, TLVar(x)>: LOcc(N) |] ==> R"
  and prem2:
    "!!y l m. [| x: LVariable; N: LTerm; y: LVariable;
         v = <Cons(0, l), TLLam(y)>; u = <Cons(0, m), TLVar(y)>;
         LBinding(<l, TLLam(y)>, <m, TLVar(y)>, N) |] ==> R"
  shows "R"
apply (rule major [THEN LBindingE])
apply (elim LOcc_LLamE LTerm_typeEs)
apply simp_all
apply safe
apply (rule prem1)
apply assumption+
apply (erule initseg_ConsE)
apply simp_all
apply (rule prem2)
prefer 4 apply assumption
prefer 3 apply (frule LOcc_domain [THEN subsetD], assumption)
apply (erule SigmaE2)
apply (erule LTag_typeEs)
apply assumption+
apply (rule LBindingI)
apply assumption+
done

lemma LBinding_LAppE:
  assumes major: "LBinding(v, u, LApp(A, B))"
  and prem1:
     "!!x l m. [| A: LTerm; B: LTerm;
         v = <Cons(0, l), TLLam(x)>; u = <Cons(0, m), TLVar(x)>;
         LBinding(<l, TLLam(x)>, <m, TLVar(x)>, A) |] ==> R"
  and prem2:
     "!!x l m. [| A: LTerm; B: LTerm;
         v = <Cons(1, l), TLLam(x)>; u = <Cons(1, m), TLVar(x)>;
         LBinding(<l, TLLam(x)>, <m, TLVar(x)>, B) |] ==> R"
  shows "R"
apply (rule major [THEN LBindingE])
apply (safe elim!: LOcc_LAppE LTerm_typeEs initseg_ConsE)
apply simp_all
apply (rule prem1)
apply assumption+
apply (rule LBindingI)
apply assumption+
apply (rule prem2)
apply assumption+
apply (rule LBindingI)
apply assumption+
done

lemmas LBinding_LTermEs = LBinding_LVarE LBinding_LLamE LBinding_LAppE

(** LBoundBy **)
lemma LBoundByI2:
  "greatest(initseg(nat),
           {n:list(nat). EX T. LBinding(<n, T>, <m, TLVar(x)>, M)}, l)
     ==> LBoundBy(<m, TLVar(x)>, <l, TLLam(x)>, M)"
apply (unfold LBoundBy_def)
apply blast
done

lemma LBoundByI:
  assumes prem1: "LBinding(<l, TLLam(x)>, <m, TLVar(x)>, M)"
  and prem2: 
     "!! n. [| <n, TLLam(x)>: LOcc(M);
         LBinding(<n, TLLam(x)>, <m, TLVar(x)>, M);
         initseg(nat, l, n) |] ==> n = l"
  shows "LBoundBy(<m, TLVar(x)>, <l, TLLam(x)>, M)"
apply (rule LBoundByI2)
apply (rule greatestI)
prefer 2
apply (rule prem1 [THEN LBindingE2])
apply (frule initsegD1)
apply (blast intro: LBindingI)
apply safe
apply (rule LBindingE, assumption)
apply (insert prem1)
apply clarsimp
apply (rename_tac l')
apply (rule_tac x1="l" and y1="l'" in chainD2 [THEN disjE])
apply (erule initsegD2 [THEN initseg_downset_forms_a_chain])
apply (blast elim!: LBindingE intro!: downsetI dest: initsegD1 initsegD2)
apply (blast elim!: LBindingE intro!: downsetI dest: initsegD1 initsegD2)
apply (drule prem2)
apply assumption+
apply hypsubst
apply assumption+
done

lemma LBoundByD1:
  "LBoundBy(u, v, M) ==> LBinding(v, u, M)"
apply (unfold LBoundBy_def)
apply safe
apply (drule greatestD1)
apply (safe elim!: LBindingE)
apply simp
apply (rule LBindingI)
apply assumption+
done

lemma LBoundByE:
  assumes major: "LBoundBy(u, v, M)"
  and prem:
     "!! x l m. [| u = <l, TLVar(x)>; v = <m, TLLam(x)>;
         LBinding(<m, TLLam(x)>, <l, TLVar(x)>, M);
         ALL n. initseg(nat, m, n) -->
                LBinding(<n, TLLam(x)>, <l, TLVar(x)>, M) --> n = m
      |] ==> R"
  shows "R"
apply (insert major major [THEN LBoundByD1])
apply (unfold LBoundBy_def)
apply (elim exE conjE)
apply (rule prem)
apply assumption+
apply hypsubst
apply safe
apply (rule greatest_unique [THEN sym], assumption)
apply (rule greatestI)
apply (rule initseg_trans)
prefer 2 apply assumption
apply (erule greatestD2)
apply assumption
apply (fast elim: initsegD2)
apply (rule poset_subset [OF Collect_subset poset_initseg])
done

lemma LBoundByE2:
  assumes major: "LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, M)"
  and prem:
     "[| LBinding(<m, TLLam(x)>, <l, TLVar(x)>, M);
         ALL n. initseg(nat, m, n) -->
                LBinding(<n, TLLam(x)>, <l, TLVar(x)>, M) --> n = m
      |] ==> R"
  shows "R"
apply (rule major [THEN LBoundByE])
apply simp
apply (elim conjE)
apply hypsubst
apply (rule prem)
apply assumption+
done

lemma LBinding_imp_LBoundBy_lemma:
  "LBinding(v, u, M) ==> EX w. LBoundBy(u, w, M)"
apply (rule LBindingE, assumption)
apply hypsubst
apply (subgoal_tac "{n: list(nat). EX T. LBinding(<n, T>, <m, TLVar(x)>, M)}
                   <= downset(initseg(nat), list(nat), m)")
prefer 2 apply (blast elim!: LBindingE intro: downsetI)
apply (rule_tac P1="{n: list(nat). EX T. LBinding(<n, T>, <m, TLVar(x)>, M)}"
         in Finite_non_empty_chain_has_greatest_element [THEN exE])
apply (rule subset_Finite)
apply assumption
apply (erule initsegD2 [THEN initseg_downset_is_Finite])
apply (erule chain_subset)
apply (erule initsegD2 [THEN initseg_downset_forms_a_chain])
apply (rule CollectI [THEN not_emptyI])
prefer 2 apply (erule exI)
apply (erule initsegD1)
apply (rule exI)
apply (erule LBoundByI2)
done

lemma LBinding_imp_LBoundBy:
  "LBinding(v, u, M) ==> EX! w. LBoundBy(u, w, M)"
apply (drule LBinding_imp_LBoundBy_lemma)
apply (erule exE)
apply (rule ex1I, assumption)
apply (unfold LBoundBy_def)
apply clarsimp
apply (drule greatest_unique, assumption)
apply (rule poset_subset [OF Collect_subset poset_initseg])
apply (erule sym)
done

lemma LBoundByE3:
  assumes major: "LBoundBy(u, v, M)"
  and prem: 
     "[| LBinding(v, u, M);
         ALL w. LBoundBy(u, w, M) --> w = v |] ==> R"
  shows "R"
apply (insert major [THEN LBoundByD1])
apply (erule LBinding_imp_LBoundBy [THEN ex1E])
apply (frule spec [THEN mp])
apply (rule major)
apply hypsubst
apply (drule LBoundByD1)
apply (rule prem)
apply assumption+
done

lemma LBinding_imp_LBoundByE:
  assumes major: "LBinding(v, <l, TLVar(x)>, M)"
  and prem: "!!m. LBoundBy(<l, TLVar(x)>, <m, TLLam(x)>, M) ==> R"
  shows "R"
apply (rule major [THEN LBinding_imp_LBoundBy, THEN ex1E])
apply (erule LBoundByE)
apply clarsimp
apply (rule prem)
apply (rule LBoundByI)
apply assumption
apply (erule spec [THEN mp, THEN mp])
apply assumption+
done


(** LBoundIn **)
lemma LBoundInI:
  "EX v. LBinding(v, u, M) ==> LBoundIn(u, M)"
apply (unfold LBoundIn_def)
apply (erule exE)
apply (erule LBindingE)
apply blast
done

lemma LBoundInE:
  "[| LBoundIn(u, M); !!v. LBinding(v, u, M) ==> R |] ==> R"
apply (unfold LBoundIn_def)
apply (blast intro: LBindingI)
done


(** LFreeIn **)
lemma LFreeInI:
  "[| M: LTerm; <m, TLVar(x)>: LOcc(M);
      !! l. [| <l, TLLam(x)>: LOcc(M);  initseg(nat, l, m) |] ==> False
   |] ==> LFreeIn(<m, TLVar(x)>, M)"
apply (unfold LFreeIn_def)
apply blast
done

lemma LFreeInI2:
  "[| M: LTerm; <m, TLVar(x)>: LOcc(M);
      !! l. LBinding(<l, TLLam(x)>, <m, TLVar(x)>, M) ==> False
   |] ==> LFreeIn(<m, TLVar(x)>, M)"
apply (blast intro: LFreeInI LBindingI)
done

lemma LFreeInD1:
  "LFreeIn(u, M) ==> M: LTerm"
apply (unfold LFreeIn_def)
apply (erule conjunct1)
done

lemma LFreeInE:
  "[| LFreeIn(u, M);
      !! l x. [| M: LTerm; u = <l, TLVar(x)>; <l, TLVar(x)>: LOcc(M);
                ALL m. <m, TLLam(x)>: LOcc(M) --> ~initseg(nat, m, l)
      |] ==> R
   |] ==> R"
apply (unfold LFreeIn_def)
apply blast
done

lemma LFreeInE2:
  assumes major: "LFreeIn(<l, TLVar(x)>, M)"
  and prem:
     "[| M: LTerm; <l, TLVar(x)>: LOcc(M);
                ALL m. <m, TLLam(x)>: LOcc(M) --> ~initseg(nat, m, l)
      |] ==> R"
  shows "R"
apply (rule major [THEN LFreeInE])
apply clarsimp
apply (rule prem)
apply assumption+
done

lemma LFreeIn_LVarI:
  "x: LVariable ==> LFreeIn(<[], TLVar(x)>, LVar(x))"
apply (rule LFreeInI2)
apply (erule_tac [3] LBinding_LTermEs)
apply (assumption | rule LTerm.intros LOcc_LTermIs)+
done

lemma LFreeIn_LLamI:
  assumes major: "LFreeIn(<l, TLVar(x)>, M)"
  and prem1: "x ~= y"
  and prem2: "y: LVariable"
  shows "LFreeIn(<Cons(0, l), TLVar(x)>, LLam(y, M))"
apply (rule major [THEN LFreeInE])
apply (rule LFreeInI2)
apply (erule_tac [3] LBinding_LTermEs)
apply (rule_tac [3] prem1 [THEN notE])
apply (assumption | rule prem1 prem2 LTerm.intros LOcc_LTermIs)+
apply simp_all
apply clarify
apply (erule LBindingE2)
apply (erule spec [THEN mp, THEN notE])
apply assumption+
done

lemma LFreeIn_LAppI1:
  "[| LFreeIn(<l, T>, M); N: LTerm |] ==>
           LFreeIn(<Cons(0, l), T>, LApp(M, N))"
apply (erule LFreeInE)
apply safe
apply (rule LFreeInI2)
apply (erule_tac [3] LBinding_LTermEs)
prefer 3 apply (clarsimp elim!: LBindingE2)
prefer 3 apply simp
apply (assumption | rule LTerm.intros LOcc_LTermIs)+
done

lemma LFreeIn_LAppI2:
  "[| LFreeIn(<l, T>, N); M: LTerm |] ==>
           LFreeIn(<Cons(1, l), T>, LApp(M, N))"
apply (erule LFreeInE)
apply safe
apply (rule LFreeInI2)
apply (erule_tac [3] LBinding_LTermEs)
prefer 4 apply (clarsimp elim!: LBindingE2)
prefer 3 apply simp
apply (assumption | rule LTerm.intros LOcc_LTermIs)+
done

lemmas LFreeIn_LTermIs = LFreeIn_LVarI LFreeIn_LLamI 
                       LFreeIn_LAppI1 LFreeIn_LAppI2

lemma LFreeIn_LVarE:
  assumes major: "LFreeIn(u, LVar(x))"
  and prem: "[| u = <[], TLVar(x)>; x: LVariable |] ==> R"
  shows "R"
apply (rule major [THEN LFreeInE])
apply (erule LOcc_LTermEs)
apply (erule LTerm_typeEs)
apply (rule prem)
apply simp_all
done

lemma LFreeIn_LLamE:
  assumes major: "LFreeIn(u, LLam(x, M))"
  and prem:
     "!!l y. [| u = <Cons(0, l), TLVar(y)>; x ~= y; x: LVariable;
        LFreeIn(<l, TLVar(y)>, M) |] ==> R"
  shows "R"
apply (rule major [THEN LFreeInE])
apply (erule LOcc_LTermEs)
apply (erule_tac [2] LTerm_typeEs)
apply (rule_tac [2] prem)
apply simp_all
apply safe
apply (rule refl)+
apply (erule spec [THEN mp, THEN notE])
apply (rule LOcc_LTermIs)
apply (rule initseg_NilI)
apply (drule LOcc_domain [THEN subsetD, THEN SigmaD1])
apply assumption
apply typecheck
apply (rule LFreeInI)
apply assumption+
apply (erule spec [THEN mp, THEN notE])
prefer 2 apply (rule initseg_ConsI)
apply (assumption | rule nat_0I LOcc_LTermIs)+
done

lemma LFreeIn_LAppE:
  assumes major: "LFreeIn(u, LApp(M, N))"
  and prem1:
     "!!l x. [| u = <Cons(0, l), TLVar(x)>; N: LTerm;
        LFreeIn(<l, TLVar(x)>, M) |] ==> R"
  and prem2:
     "!!l x. [| u = <Cons(1, l), TLVar(x)>; M: LTerm;
        LFreeIn(<l, TLVar(x)>, N) |] ==> R"
  shows "R"
apply (rule major [THEN LFreeInE])
apply (erule LOcc_LTermEs)
apply (rule_tac [3] prem2)
apply (rule_tac [2] prem1)
apply simp_all
apply (safe elim!: LTerm_typeEs)
prefer 4
prefer 5
apply (rule refl)+
apply (rule_tac [2] LFreeInI)
apply (rule LFreeInI)
apply (erule_tac [6] spec [THEN mp, THEN notE])
apply (erule_tac [3] spec [THEN mp, THEN notE])
apply (rule_tac [8] initseg_ConsI)
apply (rule_tac [4] initseg_ConsI)
apply (assumption | rule list.intros LOcc_LTermIs nat_0I nat_1I)+
done

lemmas LFreeIn_LTermEs = LFreeIn_LVarE LFreeIn_LLamE LFreeIn_LAppE


(** LBoundBy_LTerm **)

lemmas LBoundBy_LVarE = LBoundByD1 [THEN LBinding_LVarE, rule_format]

lemma LBoundBy_LLamE:
  assumes major: "LBoundBy(u, v, LLam(x, N))"
  and prem1:
     "!!l m. [| x: LVariable; N: LTerm;
          v = <[], TLLam(x)>; u = <Cons(0, m), TLVar(x)>;
          LFreeIn(<m, TLVar(x)>, N) |] ==> R"
  and prem2:
     "!!y l m. [| x: LVariable; N: LTerm; y: LVariable;
         v = <Cons(0, l), TLLam(y)>; u = <Cons(0, m), TLVar(y)>;
         LBoundBy(<m, TLVar(y)>, <l, TLLam(y)>, N) |] ==> R"
  shows "R"
apply (rule major [THEN LBoundByD1, THEN LBinding_LLamE])
apply (rule_tac [2] prem2)
apply (rule_tac [1] prem1)
apply (rule_tac [5] LFreeInI2)
apply assumption+
prefer 5 apply assumption
defer 1
apply assumption+
prefer 2
apply (insert major)

apply hypsubst
apply (erule LBoundByE2)
apply (erule LBindingE2)+
apply (drule spec [THEN mp, THEN mp])
apply (rule_tac [2] LBindingI)
apply (rule_tac [5] initseg_ConsI)
prefer 6 apply assumption
apply (rule initseg_NilI)
apply (rule list.intros)
apply (erule_tac [2] initsegD1)
prefer 3 apply (simp only: LOcc_eqns)
apply (rule Occ_consI2)
apply simp
apply simp
prefer 5 apply simp
apply (assumption | rule nat_0I)+

apply hypsubst
apply (erule LBoundByE2)
apply (rule LBoundByI)
apply assumption
apply (drule spec [THEN mp, THEN mp])
apply (rule initseg_ConsI)
prefer 2 apply assumption
apply (erule_tac [3] Cons_iff [THEN iffD1, THEN conjunct2])
apply (rule nat_0I)
apply (erule LBindingE2)+
apply (rule LBindingI)
prefer 2
apply (simp only: LOcc_eqns)
apply (rule Occ_consI2)
apply simp
apply simp
apply (assumption | rule nat_0I initseg_ConsI)+
done

lemma LBoundBy_LAppE:
  assumes major: "LBoundBy(u, v, LApp(A, B))"
  and prem1:
     "!!x l m. [| A: LTerm; B: LTerm;
         v = <Cons(0, l), TLLam(x)>; u = <Cons(0, m), TLVar(x)>;
         LBoundBy(<m, TLVar(x)>, <l, TLLam(x)>, A) |] ==> R"
  and prem2:
     "!!x l m. [| A: LTerm; B: LTerm;
         v = <Cons(1, l), TLLam(x)>; u = <Cons(1, m), TLVar(x)>;
         LBoundBy(<m, TLVar(x)>, <l, TLLam(x)>, B) |] ==> R"
  shows "R"
apply (rule major [THEN LBoundByD1, THEN LBinding_LAppE])
apply (rule_tac [2] prem2)
apply (rule_tac [1] prem1)
defer 5
apply assumption+
prefer 2
apply (insert major)

apply hypsubst
apply (erule LBoundByE2)
apply (rule LBoundByI, assumption)
apply (drule spec [THEN mp, THEN mp])
apply (erule_tac [3] Cons_iff [THEN iffD1, THEN conjunct2])
apply (rule initseg_ConsI)
apply (assumption | rule nat_0I nat_succI)+
apply (erule LBindingE2)+
apply (rule LBindingI)
prefer 2
apply (simp add: LOcc_eqns)
apply (rule Occ_consI2)
apply simp
apply simp
apply assumption+
apply (rule initseg_ConsI)
apply (assumption | rule nat_0I nat_succI)+

apply hypsubst
apply (erule LBoundByE2)
apply (rule LBoundByI, assumption)
apply (drule spec [THEN mp, THEN mp])
apply (erule_tac [3] Cons_iff [THEN iffD1, THEN conjunct2])
apply (rule initseg_ConsI)
apply (assumption | rule nat_0I nat_succI)+
apply (erule LBindingE2)+
apply (rule LBindingI)
prefer 2
apply (simp add: LOcc_eqns)
apply (rule Occ_consI2)
apply simp
apply simp
apply assumption+
apply (rule initseg_ConsI)
apply (assumption | rule nat_0I nat_succI)+

done

lemmas LBoundBy_LTermEs = LBoundBy_LVarE LBoundBy_LLamE LBoundBy_LAppE

lemma LBoundBy_LLamI1:
  "LFreeIn(<l, TLVar(x)>, M) ==>
         LBoundBy(<Cons(0, l), TLVar(x)>, <[], TLLam(x)>, LLam(x, M))"
apply (erule LFreeInE2)
apply (rule LBoundByI)
apply (rule LBindingI)
apply (rule LTerm.intros)
apply (drule LOcc_domain [THEN subsetD, THEN SigmaD2])
apply assumption
apply (erule LTag_typeEs)
apply (assumption | rule LOcc_LTermIs list.intros initseg_NilI nat_0I)+
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD1])
apply assumption
apply (erule LOcc_LTermEs)
apply simp
apply (safe elim!: LBinding_LTermEs)
apply simp
apply (erule LBindingE2)
apply (erule spec [THEN mp, THEN notE])
apply assumption+
done

lemma LBoundBy_LLamI2:
  assumes major: "LBoundBy(<l, T>, <m, U>, M)"
  and prem: "x: LVariable"
  shows "LBoundBy(<Cons(0, l), T>, <Cons(0, m), U>, LLam(x, M))"
apply (rule major [THEN LBoundByE])
apply safe
apply (rule LBoundByI)
apply (erule_tac [2] LBinding_LTermEs)
apply (safe elim!: initseg_left_ConsE)
apply simp_all
apply (erule_tac [2] spec [THEN mp, THEN mp])
apply (erule LBindingE2)
apply (rule LBindingI)
apply (assumption | rule LTerm.intros LOcc_LTermIs
        initseg_ConsI nat_0I prem)+
done

lemma LBoundBy_LAppI1:
  assumes major: "LBoundBy(<l, T>, <m, U>, M)"
  and prem: "N: LTerm"
  shows "LBoundBy(<Cons(0, l), T>, <Cons(0, m), U>, LApp(M, N))"
apply (rule major [THEN LBoundByE])
apply safe
apply (rule LBoundByI)
apply (erule_tac [2] LBinding_LTermEs)
apply (erule_tac [2] initseg_left_ConsE)
apply simp_all
apply (erule_tac [2] spec [THEN mp, THEN mp])
apply (erule LBindingE2)
apply (rule LBindingI)
apply (assumption | rule LTerm.intros LOcc_LTermIs initseg_ConsI
          nat_0I prem)+
done

lemma LBoundBy_LAppI2:
  assumes major: "LBoundBy(<l, T>, <m, U>, N)"
  and prem: "M: LTerm"
  shows "LBoundBy(<Cons(1, l), T>, <Cons(1, m), U>, LApp(M, N))"
apply (rule major [THEN LBoundByE])
apply safe
apply (rule LBoundByI)
apply (erule_tac [2] LBinding_LTermEs)
apply (erule_tac [3] initseg_left_ConsE)
apply simp_all
apply (erule_tac [2] spec [THEN mp, THEN mp])
apply (erule LBindingE2)
apply (rule LBindingI)
apply (assumption | rule LTerm.intros LOcc_LTermIs initseg_ConsI
          nat_1I prem)+
done

lemmas LBoundBy_LTermIs = LBoundBy_LLamI1 LBoundBy_LLamI2
                        LBoundBy_LAppI1 LBoundBy_LAppI2


(** LFV **)
lemma LFV_I:
  "LFreeIn(<l, TLVar(x)>, M) ==> x: LFV(M)"
apply (unfold LFV_def)
apply (rule LFreeInE2, assumption)
apply (drule LOcc_domain [THEN subsetD])
apply assumption
apply (erule SigmaE2)
apply (erule LTag_typeEs)
apply (assumption | rule CollectI exI)+
done

lemma LFV_E:
  "[| x: LFV(M); !!l. LFreeIn(<l, TLVar(x)>, M) ==> R |] ==> R"
apply (unfold LFV_def)
apply blast
done

lemma LFV_LVar:
  "x: LVariable ==> LFV(LVar(x)) = {x}"
apply (unfold LFV_def)
apply (rule equalityI)
apply (safe elim!: LFreeInE LTerm_typeEs LOcc_LTermEs)
apply simp_all
apply (rule exI)
apply (erule LFreeIn_LTermIs)
done

lemma LFV_LLam:
  "x: LVariable ==> LFV(LLam(x, N)) = LFV(N) - {x}"
apply (unfold LFV_def)
apply (rule equalityI)
apply (safe elim!: LFreeInE LTerm_typeEs LOcc_LTermEs)
apply simp_all
apply (rule exI)
apply (rule LFreeInI2)
apply assumption+
apply (clarify elim!: LBindingE2)
apply (erule spec [THEN mp, THEN notE])
apply (rule_tac [2] initseg_ConsI)
apply (erule LOcc_LTermIs)
apply (rule nat_0I)
apply assumption

apply (erule spec [THEN mp, THEN notE])
apply (rule LOcc_LTermIs)
apply (rule initseg_NilI)
apply (rule list.intros nat_0I)+
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD1])
apply assumption

apply (rule exI)
apply (rule LFreeIn_LTermIs)
apply (rule LFreeInI2)
apply assumption+
apply (erule LBindingE2)
apply (erule spec [THEN mp, THEN notE])
apply assumption+
done

lemma LFV_LApp:
  "[| M: LTerm; N: LTerm |] ==> LFV(LApp(M, N)) = LFV(M) Un LFV(N)"
apply (unfold LFV_def)
apply (rule equalityI)
apply (safe elim!: LFreeInE LTerm_typeEs LOcc_LTermEs)
apply simp_all

apply (rule exI)
apply (rule LFreeInI2)
apply assumption+
apply (erule LBindingE2)
apply (erule spec [THEN mp, THEN notE])
apply (erule LOcc_LTermIs)
apply (rule initseg_ConsI)
apply (rule nat_0I nat_1I)
apply assumption

apply (erule spec [THEN notE])
apply (rule LFreeInI2)
apply assumption+
apply (erule LBindingE2)
apply (erule spec [THEN mp, THEN notE])
apply (erule LOcc_LTermIs)
apply (rule initseg_ConsI)
apply (rule nat_0I nat_1I)
apply assumption

apply (rule exI)
apply (rule LFreeInI2)
apply (typecheck add: LTerm.intros)
apply (erule LOcc_LTermIs)
apply (erule LBinding_LTermEs)
apply clarsimp
apply (erule LBindingE2)
apply (erule spec [THEN mp, THEN notE])
apply assumption+
apply simp

apply (rule exI)
apply (rule LFreeInI2)
apply (typecheck add: LTerm.intros)
apply (erule LOcc_LTermIs)
apply (erule LBinding_LTermEs)
apply simp
apply clarsimp
apply (erule LBindingE2)
apply (erule spec [THEN mp, THEN notE])
apply assumption+

done


(** LFO **)
lemma LFO_I:
  "LFreeIn(<l, TLVar(x)>, M) ==> <l, TLVar(x)>: LFO(x, M)"
apply (unfold LFO_def)
apply (rule LFreeInE2, assumption)
apply (drule LOcc_domain [THEN subsetD])
apply assumption
apply (assumption | rule CollectI exI conjI refl)+
done

lemma LFO_E:
  "[| u: LFO(x, M);
     !!l. [| u = <l, TLVar(x)>; LFreeIn(<l, TLVar(x)>, M) |] ==> R
   |] ==> R"
apply (unfold LFO_def)
apply blast
done

lemma LFO_E2:
  assumes major: "<l, TLVar(y)>: LFO(x, M)"
  and prem: "[| y = x; LFreeIn(<l, TLVar(x)>, M) |] ==> R"
  shows "R"
apply (rule major [THEN LFO_E])
apply simp
apply (rule prem)
apply (erule conjunct2)
apply simp
done

lemma LFO_LVar1:
  "x: LVariable ==> LFO(x, LVar(x)) = {<[], TLVar(x)>}"
apply (unfold LFO_def)
apply (rule equalityI)
apply (safe elim!: LFreeInE LTerm_typeEs LOcc_LTermEs LTag.free_elims)
apply (rule exI)
apply (assumption | rule conjI refl LFreeIn_LTermIs)+
done

lemma LFO_LVar2:
  "x ~= y ==> LFO(x, LVar(y)) = 0"
apply (unfold LFO_def)
apply (rule equalityI)
apply (safe elim!: LFreeInE LTerm_typeEs LOcc_LTermEs LTag.free_elims)
done

lemma LFO_LLam1:
  "LFO(x, LLam(x, M)) = 0"
apply (unfold LFO_def)
apply (rule equalityI)
apply (safe elim!: LFreeIn_LTermEs LTerm_typeEs LOcc_LTermEs LTag.free_elims)
done

lemma LFO_LLam2:
  "[| x ~= y; y: LVariable |]
      ==> LFO(x, LLam(y, M)) = Occ_shift(0, LFO(x, M))"
apply (unfold LFO_def)
apply (rule equalityI)
apply (safe elim!: LFreeIn_LTermEs ConsE Occ_shiftE LTerm_typeEs
                   LOcc_LTermEs LTag.free_elims
            intro!: Occ_shiftI)
apply (intro exI conjI)
apply (rule refl)
apply assumption

apply (intro exI conjI)
apply (rule refl)
apply (erule LFreeIn_LTermIs)
apply assumption+

done

lemma LFO_LApp:
  "[| M: LTerm; N: LTerm |] ==>
   LFO(x, LApp(M, N)) = Occ_shift(0, LFO(x, M)) Un Occ_shift(1, LFO(x, N))"
apply (unfold LFO_def)
apply (rule equalityI)
apply (safe elim!: LFreeIn_LTermEs ConsE Occ_shiftE LTerm_typeEs
                   LOcc_LTermEs LTag.free_elims
            intro!: Occ_shiftI)

apply (intro exI conjI)
apply (rule refl)
apply assumption

apply (intro exI conjI)
apply (rule refl)
apply assumption

apply (intro exI conjI)
apply (rule refl)
apply (erule LFreeIn_LTermIs)
apply assumption+

apply (intro exI conjI)
apply (rule refl)
apply (erule LFreeIn_LTermIs)
apply assumption

done

lemmas LFV_eqns = LFV_LVar LFV_LLam LFV_LApp
lemmas LFO_eqns = LFO_LVar1 LFO_LVar2 LFO_LLam1 LFO_LLam2 LFO_LApp


(** Lsubst **)
lemma LFO_subset_LOcc:
  "LFO(x, M) <= LOcc(M)"
apply (unfold LFO_def)
apply (blast elim!: LFreeInE LTag.free_elims)
done

lemma Incomparable_LFO:
  "M: LTerm ==> Incomparable(domain(LFO(x, M)))"
apply (unfold LFO_def)
apply (rule Incomparable_subset)
apply (rule Incomparable_CorrectArity_0)
apply (erule LOcc_domain)
apply (erule LOcc_in_Occ_range [THEN Occ_range_DenseTreeD])
apply (rule domain_mono)
apply (safe elim!: LFreeInE LTag.free_elims)
apply (drule LOcc_in_Occ_range [THEN Occ_range_CorrectArityD], assumption)
apply simp
done

lemma LFO_LLam_not_Nil:
  "y: LVariable ==> domain(LFO(x, LLam(y, M))) ~= {[]}"
apply (case_tac "x = y")
apply hypsubst
apply (simp add: LFO_eqns)
apply (simp add: LFO_eqns)
apply (rule notI)
apply (drule equalityD2 [THEN singleton_subsetD])
apply (blast elim!: Occ_shiftE list.free_elims)
done

lemma LFO_LApp_not_Nil:
  "[| M: LTerm; N: LTerm |] ==> domain(LFO(x, LApp(M, N))) ~= {[]}"
apply (simp add: LFO_eqns)
apply (rule notI)
apply (drule equalityD2 [THEN singleton_subsetD])
apply (blast elim!: Occ_shiftE list.free_elims)
done

lemmas LTerm_def_graft_type = def_graft_type [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LOccinv_def Lgraft_def]

lemma Lsubst_type:
  "[| M: LTerm; N: LTerm |] ==> Lsubst(M, x, N): LTerm"
apply (unfold Lsubst_def)
apply (rule LTerm_def_graft_type)
apply (assumption | rule Incomparable_LFO domain_mono LFO_subset_LOcc)+
done

lemmas LTerm_def_graft_Nil = def_graft_Nil [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LOccinv_def Lgraft_def]

lemma Lsubst_LVar1:
  "[| x: LVariable; N: LTerm |] ==> Lsubst(LVar(x), x, N) = N"
apply (unfold Lsubst_def)
apply (simp only: LFO_eqns)
apply (simp add: LTerm_def_graft_Nil LTerm_cons_eqns_sym)
done

lemmas LTerm_def_graft_0 = def_graft_0 [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LOccinv_def Lgraft_def]

lemma Lsubst_LVar2:
  "[| x ~= y; y: LVariable |] ==> Lsubst(LVar(y), x, N) = LVar(y)"
apply (unfold Lsubst_def)
apply (simp add: LFO_eqns)
apply (simp add: LTerm_def_graft_0 LTerm_cons_eqns_sym)
done

lemma Lsubst_LLam1:
  "[| x: LVariable; M: LTerm |] ==> Lsubst(LLam(x, M), x, N) = LLam(x, M)"
apply (unfold Lsubst_def)
apply (simp only: LFO_eqns)
apply (simp add: LTerm_def_graft_0 LTerm_cons_eqns_sym)
done

lemmas LTerm_def_graft = def_graft [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LTerm_Term_cons_inj_cond
  LOccinv_def Lgraft_def]

lemma Lsubst_LLam2:
  "[| x ~= y; y: LVariable; M: LTerm; N: LTerm |] ==>
       Lsubst(LLam(y, M), x, N) = LLam(y, Lsubst(M, x, N))"
apply (unfold Lsubst_def)
apply (subgoal_tac "domain(LFO(x, LLam(y, M))) ~= {[]}"
                   "Incomparable(domain(LFO(x, LLam(y, M))))"
                   "domain(LFO(x, LLam(y, M))) <= domain(LOcc(LLam(y, M)))"
                   "LFO(x, M) <= list(nat) * LTag")
apply (simp add: LFO_eqns)
apply (simp add: LTerm_def_graft LTerm_cons_eqns_sym lists_subtree_domain_eq
                 Occ_subtree_simps)
apply (rule LFO_subset_LOcc [THEN subset_trans])
apply (assumption | rule LOcc_domain LFO_subset_LOcc domain_mono
         Incomparable_LFO LFO_LLam_not_Nil LTerm.intros)+
done

lemma Lsubst_LApp:
  "[| A: LTerm; B: LTerm; N: LTerm |] ==>
       Lsubst(LApp(A, B), x, N) = LApp(Lsubst(A, x, N), Lsubst(B, x, N))"
apply (unfold Lsubst_def)
apply (subgoal_tac "domain(LFO(x, LApp(A, B))) ~= {[]}"
                   "Incomparable(domain(LFO(x, LApp(A, B))))"
                   "domain(LFO(x, LApp(A, B))) <= domain(LOcc(LApp(A, B)))"
                   "LFO(x, A) <= list(nat) * LTag"
                   "LFO(x, B) <= list(nat) * LTag")
apply (simp only: LFO_eqns)
apply (simp add: LTerm_def_graft LTerm_cons_eqns_sym lists_subtree_domain_eq
                 Occ_subtree_simps del: domain_Un_eq)
apply (assumption | rule subset_trans [OF LFO_subset_LOcc LOcc_domain]
        LFO_subset_LOcc domain_mono Incomparable_LFO LFO_LApp_not_Nil LTerm.intros)+
done

lemma Lsubst_0:
  "[| M: LTerm; x ~: LFV(M) |] ==> Lsubst(M, x, N) = M"
apply (unfold Lsubst_def)
apply (rule_tac P="%x. Lgraft(M, x, N) = M" in subst)
apply (erule_tac [2] LTerm_def_graft_0)
apply (rule equalityI)
apply blast
apply (rule subsetI)
apply (erule notE)
apply (blast elim!: LFO_E intro: LFV_I)
done

lemmas Lsubst_eqns = Lsubst_LVar1 Lsubst_LVar2 Lsubst_LLam1 Lsubst_LLam2
                   Lsubst_LApp Lsubst_0

lemmas LTerm_ss_simps = Lsubst_eqns LFV_eqns LFO_eqns
declare LTerm_ss_simps [simp]
declare Lsubst_type [TC]
declare LTerm.intros [TC]

lemma Lsubst_self:
  assumes prem1: "x: LVariable"
  and prem2: "M: LTerm"
  shows "Lsubst(M, x, LVar(x)) = M"
apply (insert prem1 [THEN LTerm.intros(1)])
apply (rule prem2 [THEN LTerm.induct])
apply (rename_tac [2] v)
apply (rename_tac v)
apply (case_tac [2] "x = v")
apply (case_tac "x = v")
apply simp_all
done


(** LFreeForIn **)
lemma LFreeForInE:
  "[| LFreeForIn(N, x, M);
      [| M: LTerm; N: LTerm; x: LVariable;
         ALL z l m. z: LFV(N) & LFreeIn(<l, TLVar(x)>, M) &
         <m, TLLam(z)>: LOcc(M) & initseg(nat, m, l) --> False
      |] ==> R
   |] ==> R"
apply (unfold LFreeForIn_def)
apply blast
done

lemma LFreeForInD1:
  "LFreeForIn(N, x, M) ==> N: LTerm"
apply (unfold LFreeForIn_def)
apply (erule conjunct1)
done

lemma LFreeForInD2:
  "LFreeForIn(N, x, M) ==> x: LVariable"
apply (unfold LFreeForIn_def)
apply (erule conjunct2 [THEN conjunct1])
done

lemma LFreeForInD3:
  "LFreeForIn(N, x, M) ==> M: LTerm"
apply (unfold LFreeForIn_def)
apply (erule conjunct2 [THEN conjunct2, THEN conjunct1])
done

lemma LFreeForInI:
  "[| N: LTerm; x: LVariable; M: LTerm;
      !! z l m. [| z: LFV(N); LFreeIn(<l, TLVar(x)>, M);
        <m, TLLam(z)>: LOcc(M); initseg(nat, m, l) |] ==> False
   |] ==> LFreeForIn(N, x, M)"
apply (unfold LFreeForIn_def)
apply blast
done

lemma LFreeForIn_LVarI:
  "[| x: LVariable; y: LVariable; N: LTerm |]
          ==>  LFreeForIn(N, x, LVar(y))"
apply (rule LFreeForInI)
prefer 4
apply (erule LOcc_LTermEs)
apply simp
apply (assumption | rule LTerm.intros)+
done

lemma LFreeForIn_LLamI1:
  "[| N: LTerm; x: LVariable; M: LTerm |] ==>
        LFreeForIn(N, x, LLam(x, M))"
apply (rule LFreeForInI)
prefer 4
apply (erule LFreeIn_LTermEs)
apply (blast elim!: LTag.free_elims)
apply (assumption | rule LTerm.intros)+
done

lemma LFreeForIn_LLamI2:
  assumes prem1: "y: LVariable"
  and prem2: "LFreeForIn(N, x, M)"
  and prem3: "[| y: LFV(N); x: LFV(M); y ~= x |] ==> False"
  shows "LFreeForIn(N, x, LLam(y, M))"
apply (rule prem2 [THEN LFreeForInE])
apply (rule LFreeForInI)
apply (safe elim!: LFreeIn_LTermEs initseg_left_ConsE
              LTag.free_elims LOcc_LTermEs list.free_elims)
apply (rule_tac [2] prem3)
apply (erule_tac [5] spec [THEN spec, THEN spec, THEN mp])
apply (assumption | rule LTerm.intros LFV_I conjI prem1)+
done

lemma LFreeForIn_LLamI3:
  "[| x ~: LFV(M); M: LTerm; N: LTerm; x: LVariable; y: LVariable |] ==>
          LFreeForIn(N, x, LLam(y, M))"
apply (rule LFreeForInI)
apply (assumption | rule LTerm.intros)+
apply (safe elim!: LOcc_LTermEs LFreeIn_LTermEs LTag.free_elims
              initseg_left_ConsE list.free_elims)
apply (erule notE, erule LFV_I)+
done

lemma LFreeForIn_LAppI:
  assumes prem1: "LFreeForIn(N, x, A)"
  and prem2: "LFreeForIn(N, x, B)"
  shows "LFreeForIn(N, x, LApp(A, B))"
apply (rule prem1 [THEN LFreeForInE])
apply (rule prem2 [THEN LFreeForInE])
apply (rule LFreeForInI)
apply (assumption | rule LTerm.intros)+
apply (safe elim!: LFreeIn_LTermEs initseg_left_ConsE
         LTag.free_elims LOcc_LTermEs list.free_elims)
apply (erule spec [THEN spec, THEN spec, THEN mp])
apply (assumption | rule conjI)+
apply (erule spec [THEN spec, THEN spec, THEN mp],
  rule conjI, assumption, rule conjI, assumption)
apply (assumption | rule conjI)+
done

lemmas LFreeForIn_LTermIs = LFreeForIn_LVarI LFreeForIn_LLamI1
                          LFreeForIn_LLamI2 LFreeForIn_LAppI

lemma LFreeForIn_LVarE:
  "[| LFreeForIn(N, x, LVar(y));
      [| x: LVariable; y: LVariable; N: LTerm |] ==> R |] ==> R"
apply (erule LFreeForInE)
apply (erule LTerm_typeEs)
apply blast
done

lemma LFreeForIn_LLamE:
  assumes major: "LFreeForIn(N, x, LLam(y, M))"
  and prem1: "[| x = y; x: LVariable; N: LTerm; M: LTerm |] ==> R"
  and prem2: "[| x ~= y; y: LVariable; LFreeForIn(N, x, M);
                 x: LFV(M); y ~: LFV(N) |] ==> R"
  and prem3: "[| x ~= y; y: LVariable; N: LTerm; x: LVariable; x ~: LFV(M)|] ==> R"
  shows "R"
apply (rule major [THEN LFreeForInE])
apply (erule LTerm_typeEs)
apply (case_tac "x = y")
apply (rule prem1)
apply assumption+
apply (case_tac "x: LFV(M)")
prefer 2
apply (rule prem3)
apply assumption+
apply (erule LFV_E)
apply (rule prem2)
apply (rule_tac [3] LFreeForInI)
apply assumption+
apply (erule_tac spec [THEN spec, THEN spec, THEN mp])
apply (intro conjI)
apply (rule_tac [4] initseg_ConsI)
prefer 5 apply assumption
apply (rule_tac [2] LFreeIn_LTermIs)
apply (assumption | rule nat_0I LFV_I LOcc_LTermIs)+
apply (rule notI)
apply (erule spec [THEN spec, THEN spec, THEN mp])
apply (assumption | rule conjI nat_0I initseg_NilI LOcc_LTermIs
           LFreeIn_LTermIs list.intros)+
apply (erule LFreeInE2)
apply (rule LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption
done

lemma LFreeForIn_LAppE:
  assumes major: "LFreeForIn(N, x, LApp(A, B))"
  and prem: "[| LFreeForIn(N, x, A); LFreeForIn(N, x, B) |] ==> R"
  shows "R"
apply (rule major [THEN LFreeForInE])
apply (erule LTerm_typeEs)
apply (rule prem)
apply (erule_tac [2] LFreeForInI)
apply (erule LFreeForInI)
defer 3
apply assumption+
prefer 2
apply (erule_tac [2] spec [THEN spec, THEN spec, THEN mp])
apply (erule_tac [1] spec [THEN spec, THEN spec, THEN mp])
apply (erule LFreeIn_LTermIs LOcc_LTermIs | assumption |
       rule conjI initseg_ConsI nat_0I nat_1I)+
done

lemmas LFreeForIn_LTermEs = LFreeForIn_LVarE LFreeForIn_LLamE
                          LFreeForIn_LAppE

lemma LFreeForIn_left_LVarI:
  "[| x: LVariable; M: LTerm |] ==> LFreeForIn(LVar(x), x, M)"
apply (rule LFreeForInI)
apply (erule_tac [4] LFreeInE2)
apply (safe elim!: LFreeIn_LTermEs LFV_E LTag.free_elims)
apply (erule spec [THEN mp, THEN notE])
apply (assumption | rule LTerm.intros)+
done

lemma TLVar_free_or_bound:
  assumes prem1: "<l, TLVar(x)>: LOcc(M)"
  and prem2: "M: LTerm"
  shows "LFreeIn(<l, TLVar(x)>, M) | LBoundIn(<l, TLVar(x)>, M)"
apply (case_tac "LBoundIn(<l, TLVar(x)>, M)")
prefer 2
apply (rule disjI1)
apply (rule LFreeInI2)
apply (erule_tac [3] notE)
apply (rule_tac [3] LBoundInI)
apply (assumption | rule prem1 prem2 exI disjI2)+
done

lemma DenseTree_CorrectArity_0D:
  assumes hier: "DenseTree(X)"
  and corrT: "CorrectArity(X, T, 0)"
  and prem1: "<l, T>: X"
  and prem2: "<m, U>: X"
  and prem3: "initseg(nat, l, m)"
  shows "l = m"
apply (rule prem3 [THEN initsegE])
apply (erule_tac a="x" in list.cases)
apply simp
apply hypsubst
apply (rule hier [THEN DenseTreeE])
apply (rule prem2)
apply hypsubst
apply (assumption | rule initseg_appI2 initseg_ConsI initseg_NilI)+
apply (rule corrT [THEN CorrectArityD2, THEN notE])
apply (assumption | rule prem1 exI nat_into_Ord [THEN Ord_0_le])+
done

lemma TLVar_leaf:
  "[| <l, TLVar(x)>: LOcc(M); <m, T>: LOcc(M); initseg(nat, l, m);
       M: LTerm |] ==> m = l & T = TLVar(x)"
apply (frule LOcc_in_Occ_range)
apply (erule Occ_rangeE)
apply (subgoal_tac "m = l")
apply (erule_tac [2] DenseTree_CorrectArity_0D [THEN sym])
apply (drule_tac [2] x="TLVar(x)" in bspec)
prefer 3 apply simp
apply (erule_tac [2] LOcc_typeD2)
apply safe
apply (erule functionalD)
apply assumption+
done

lemmas LTerm_Occ_Graft_in_Occ_range2 = Occ_Graft_in_Occ_range2 [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond]

lemmas LTerm_def_Occ_Occinv = def_Occ_Occinv [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LOccinv_def]

lemma LOcc_LsubstE:
  assumes major: "u: LOcc(Lsubst(M, x, N))"
  and M_term: "M: LTerm"
  and N_term: "N: LTerm"
  and prem1:
     "!! l T. [| u = <l, T>; <l, T>: LOcc(M); <l, T> ~: LFO(x, M) |]
             ==> R"
  and prem2:
     "!!m l T. [| u = <m @ l, T>; <m, TLVar(x)>: LFO(x, M);
          <l, T>: LOcc(N) |] ==> R"
  shows "R"
apply (insert M_term N_term)
apply (subgoal_tac "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N))
                        : Occ_range(LTag, LArity)")
prefer 2
apply (assumption | rule LTerm_Occ_Graft_in_Occ_range2
        LOcc_in_Occ_range Incomparable_LFO
        LFO_subset_LOcc [THEN domain_mono])+
apply (insert major)
apply (unfold Lsubst_def Lgraft_def)
apply (simp only: LTerm_def_Occ_Occinv)
apply (erule Occ_GraftE)
apply (erule LOcc_domain)
apply (erule_tac [2] Occ_ShiftE)
apply (erule_tac [2] domainE)
apply (rule_tac [2] prem2)
apply (rule prem1)
apply (safe elim!: LFO_E LTag.free_elims)
apply (erule_tac [5] LFO_I)
apply (rule refl)
prefer 3 apply (rule refl)
apply assumption
prefer 2 apply assumption
apply (erule notE)
apply (rule bexI)
apply (erule_tac [2] LFO_I [THEN domainI])
apply (assumption | rule initseg_refl)+
done

lemma LOcc_LsubstI1:
  "[| <l, T> ~: LFO(x, M); <l, T>: LOcc(M); M: LTerm; N: LTerm |]
     ==> <l, T>: LOcc(Lsubst(M, x, N))"
apply (subgoal_tac "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N))
                        : Occ_range(LTag, LArity)")
prefer 2
apply (assumption | rule LTerm_Occ_Graft_in_Occ_range2
        LOcc_in_Occ_range Incomparable_LFO
        LFO_subset_LOcc [THEN domain_mono])+
apply (unfold Lsubst_def Lgraft_def)
apply (simp only: LTerm_def_Occ_Occinv)
apply (rule Occ_GraftI1)
apply assumption
apply (safe elim!: LFO_E LFreeInE2)
apply (rename_tac l')
apply (subgoal_tac "TLVar(x): LTag" "l' = l" "T = TLVar(x)")
prefer 4
apply (rule LOcc_domain [THEN subsetD, THEN SigmaD2])
prefer 2 apply assumption
apply assumption

prefer 3
apply (rule LOcc_in_Occ_range [THEN Occ_rangeE])
apply assumption
apply (erule DenseTree_CorrectArity_0D)
apply (drule_tac x="TLVar(x)" in bspec)
prefer 2 apply simp
apply (assumption | rule LTag.intros)+

prefer 2
apply hypsubst
apply (erule LOcc_in_Occ_range [THEN Occ_range_functionalD,
        THEN functionalD])
apply assumption+

apply hypsubst
apply (erule notE)
apply (rule LFreeInI [THEN LFO_I])
apply (erule_tac [3] spec [THEN mp, THEN notE])
apply assumption+
done

lemma LOcc_LsubstI2:
  "[| <m, TLVar(x)>: LFO(x, M); <l, T>: LOcc(N); M: LTerm; N: LTerm |]
      ==> <m @ l, T>: LOcc(Lsubst(M, x, N))"
apply (subgoal_tac "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N))
                        : Occ_range(LTag, LArity)")
prefer 2
apply (assumption | rule LTerm_Occ_Graft_in_Occ_range2
        LOcc_in_Occ_range Incomparable_LFO
        LFO_subset_LOcc [THEN domain_mono])+
apply (unfold Lsubst_def Lgraft_def)
apply (simp only: LTerm_def_Occ_Occinv)
apply (rule Occ_GraftI2)
apply (erule domainI)
apply (erule Occ_ShiftI)
done

lemma LBoundBy_LsubstE:
  assumes major: "LBoundBy(<l, TLVar(y)>, <m, TLLam(y)>, Lsubst(M, x, N))"
  and sub: "LFreeForIn(N, x, M)"
  and prem1: "LBoundBy(<l, TLVar(y)>, <m, TLLam(y)>, M) ==> R"
  and prem2:
     "!!n a b. [| l =  n @ a; m = n @ b; <n, TLVar(x)>: LFO(x, M);
        LBoundBy(<a, TLVar(y)>, <b, TLLam(y)>, N) |] ==> R"
  shows "R"
apply (rule sub [THEN LFreeForInE])
apply (subgoal_tac "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N))
                        : Occ_range(LTag, LArity)")
apply (insert major)
prefer 2
apply (assumption | rule LTerm_Occ_Graft_in_Occ_range2
        LOcc_in_Occ_range Incomparable_LFO
        LFO_subset_LOcc [THEN domain_mono])+
apply (unfold Lsubst_def Lgraft_def)
apply (erule LBoundByE)
apply (erule LBindingE2)
apply (simp only: LTerm_def_Occ_Occinv)
apply (elim Occ_ShiftE2 LOcc_domain [THEN [2] Occ_GraftE])
prefer 7
apply assumption+

prefer 4
apply hypsubst
apply (erule initseg_left_appE)
apply (erule domainE)
apply (erule subset_trans [OF LFO_subset_LOcc LOcc_domain,
         THEN subsetD, THEN SigmaD1])
apply assumption
apply (rule_tac [2] prem1)
apply (rule prem2)
apply (safe elim!: LFO_E LTag.free_elims intro!: LFO_I)
apply (assumption | rule refl)+
defer 1

prefer 3
apply (erule notE)
apply (rename_tac l')
apply (subgoal_tac "l': list(nat)")
prefer 2
apply (erule LFreeInE2)
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD1])
apply assumption
apply (rule bexI)
apply (erule_tac [2] LFO_I [THEN domainI])
apply (erule initseg_left_appE)
apply assumption
apply hypsubst
apply (rule initseg_appI1)
apply (erule_tac [2] app_typeD)
apply assumption+

prefer 2
apply (rename_tac l')
apply (subgoal_tac "l': list(nat)")
apply (erule_tac [2] LFreeInE2)
apply (erule_tac [2] LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply (erule initseg_right_appE)
apply (erule_tac [3] notE)
apply (rule_tac [3] bexI)
prefer 3 apply assumption
apply (erule_tac [3] LFO_I [THEN domainI])
apply assumption
apply (erule TLVar_free_or_bound [THEN disjE])
apply assumption
apply (drule spec [THEN spec, THEN spec, THEN mp])
apply (assumption | rule conjI LFV_I)+
apply (erule FalseE)
apply (erule LBoundInE)
apply (drule LBinding_imp_LBoundBy_lemma)
apply (erule exE)
apply (erule LBoundByE)
apply (safe elim!: LTag.free_elims LBindingE2)
apply (drule spec [THEN mp, THEN mp])
apply (rule_tac [2] LBindingI)
apply (rule_tac [5] initseg_appI2)
prefer 6 apply assumption
apply (rule initseg_trans)
apply assumption
apply (rule_tac initseg_appI1)
apply (erule_tac [2] initsegD1)
prefer 3 apply (simp only: LTerm_def_Occ_Occinv)
prefer 4 apply (simp only: LTerm_def_Occ_Occinv)
prefer 2 apply (rule Occ_GraftI2)
apply (erule LFO_I [THEN domainI])
apply (erule Occ_ShiftI)
apply (rule Occ_GraftI2)
apply (erule LFO_I [THEN domainI])
apply (erule Occ_ShiftI)
apply assumption+
apply hypsubst
apply (erule initseg_left_appE)
apply (drule_tac [2] sym [THEN app_Nil_eqD1])
prefer 3 apply hypsubst
apply (erule initseg_NilE)
apply hypsubst
apply (subgoal_tac "TLLam(y) = TLVar(x)")
apply (erule_tac [2] LOcc_in_Occ_range [THEN Occ_range_functionalD, THEN functionalD])
prefer 2 apply assumption
apply (erule_tac [2] LFreeInE)
prefer 2 apply simp
apply (blast elim!: LTag.free_elims)
apply assumption+

prefer 2
apply (rule_tac [2] LBoundByI)
apply (rule_tac [2] LBindingI)
apply (rule LBoundByI)
apply (rule LBindingI)

prefer 4
prefer 6
prefer 7
prefer 8
prefer 9
apply assumption+

apply (clarify elim!: LTag.free_elims LFreeInE)
apply (erule app_appE)
apply (assumption | rule LOcc_domain [THEN subsetD, THEN SigmaD1])+
apply hypsubst
apply (erule_tac a="z" in list.cases)
apply hypsubst
apply simp
prefer 2
apply (erule_tac a="z" in list.cases)
apply hypsubst
apply simp

apply hypsubst
apply (erule LOcc_in_Occ_range [THEN Occ_rangeE])
apply (rename_tac l' x'' l''' x' z a l'')
apply (erule_tac l="l' @ Cons(a, l'')" in DenseTreeE)
apply (rule_tac [2] initseg_appI2)
apply (rule_tac [3] initseg_ConsI)
apply (rule_tac [4] initseg_NilI)
apply (rule_tac [2] LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 3 apply assumption
apply assumption+
apply (erule bspec [THEN CorrectArityD2, THEN notE])
apply (erule_tac [4] exI)
prefer 2 apply assumption
prefer 2 apply simp
apply (erule LTag.intros)

apply hypsubst
apply (erule LOcc_in_Occ_range [THEN Occ_rangeE])
apply (rename_tac l' x' z a l'')
apply (erule_tac l="l' @ Cons(a, l'')" in DenseTreeE)
apply (rule_tac [2] initseg_appI2)
apply (rule_tac [3] initseg_ConsI)
apply (rule_tac [4] initseg_NilI)
apply (rule_tac [2] LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 3 apply assumption
apply assumption+
apply (erule bspec [THEN CorrectArityD2, THEN notE])
apply (erule_tac [4] exI)
prefer 2 apply assumption
prefer 2 apply simp
apply (erule LTag.intros)

apply (rename_tac l' y' l'' n)
apply (subgoal_tac "l': list(nat)")
prefer 2 apply (elim LFreeInE2)
apply (rule LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption
apply (rule app_right_inj_iff [THEN iffD1])
apply (erule_tac [2] spec [THEN mp, THEN mp])
apply (rule_tac [2] initseg_appI2)
apply assumption+
apply (rule LBindingI)
prefer 4
apply (erule_tac [1] ssubst)
apply (rule_tac [1] initseg_appI2)
apply (erule_tac [2] LBindingE2)
apply assumption+
prefer 3
apply (erule spec [THEN mp, THEN mp])
apply (rule_tac [2] LBindingI)
apply (erule_tac [5] LBindingE2)
prefer 5
apply assumption+
apply (simp_all only: LTerm_def_Occ_Occinv)
prefer 4 apply (erule LBindingE2)
prefer 4 apply (erule LBindingE2)
prefer 4 apply (erule LBindingE2)
prefer 4 apply (erule LBindingE2)

prefer 3
apply (rule Occ_GraftI2)
apply (erule_tac [2] Occ_ShiftI)
apply (erule LFO_I [THEN domainI])
prefer 3
apply (rule Occ_GraftI2)
apply (erule_tac [2] Occ_ShiftI)
apply (erule LFO_I [THEN domainI])

apply (rule Occ_GraftI1)
apply assumption
apply (rule notI)
apply (erule bexE)
apply (erule notE)
apply (erule notE)
apply (rule bexI)
prefer 2 apply assumption
apply (erule initseg_trans)
apply assumption

apply (rule Occ_GraftI1)
apply assumption+
done

lemmas LTerm_def_Occinv_type = def_Occinv_type [OF
  LTerm_Occ_cons_cond LTerm_Occ_ind_cond LOccinv_def]

lemma LBoundBy_LsubstI1:
  assumes major: "LBoundBy(<l, TLVar(y)>, <m, TLLam(y)>, M)"
  and prem: "N: LTerm"
  shows "LBoundBy(<l, TLVar(y)>, <m, TLLam(y)>, Lsubst(M, x, N))"
apply (rule major [THEN LBoundByE2])
apply (erule LBindingE2)
apply (subgoal_tac "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N))
                        : Occ_range(LTag, LArity)")
prefer 2
apply (assumption | rule LTerm_Occ_Graft_in_Occ_range2
        LOcc_in_Occ_range Incomparable_LFO
        LFO_subset_LOcc [THEN domain_mono] prem)+
apply (unfold Lsubst_def Lgraft_def)
apply (rule LBoundByI)
apply (erule_tac [2] LBindingE2)
apply (rule LBindingI)
apply (simp_all only: LTerm_def_Occ_Occinv)
apply (erule LTerm_def_Occinv_type)
apply (rule_tac [2] Occ_GraftI1)
apply (rule Occ_GraftI1)
prefer 3
apply assumption+
apply (rule notI)
apply (rule_tac [2] notI)
apply (safe elim!: LFO_E LFreeInE2)

apply (rule LOcc_in_Occ_range [THEN Occ_rangeE])
apply assumption
apply (drule_tac T="TLVar(x)" in DenseTree_CorrectArity_0D)
prefer 2 apply assumption
prefer 3 apply assumption
prefer 2 apply assumption
apply (drule_tac x="TLVar(x)" in bspec)
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD2])
apply assumption
apply simp
apply hypsubst
apply (subgoal_tac "TLLam(y) = TLVar(x)")
apply (blast elim!: LTag.free_elims)
apply (erule functionalD)
apply assumption+

apply (rule LOcc_in_Occ_range [THEN Occ_rangeE])
apply assumption
apply (drule_tac T="TLVar(x)" in DenseTree_CorrectArity_0D)
prefer 2 apply assumption
prefer 3 apply assumption
prefer 2 apply assumption
apply (drule_tac x="TLVar(x)" in bspec)
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD2])
apply assumption
apply simp
apply hypsubst
apply (subgoal_tac "TLVar(y) = TLVar(x)")
apply simp
apply (erule functionalD)
apply assumption+

apply (erule spec [THEN mp, THEN mp])
apply assumption
apply (safe elim!: LTag.free_elims LOcc_domain [THEN [2] Occ_GraftE]
             Occ_ShiftE)
(* apply (rename_tac [3] m' l' T y' l'' U) *)
apply (subgoal_tac [3] "ma: list(nat)")
prefer 4
apply (erule subset_trans [OF LFO_subset_LOcc LOcc_domain,
          THEN subsetD, THEN SigmaD1])
apply assumption
(* apply (rename_tac [4] m' l' T y' m'' l'' U y'') *)
apply (subgoal_tac [4] "ma: list(nat)")
prefer 5
apply (erule subset_trans [OF LFO_subset_LOcc LOcc_domain,
          THEN subsetD, THEN SigmaD1])
apply assumption

prefer 3
apply (erule initseg_left_appE)
apply assumption
apply hypsubst
apply (erule notE)
apply (rule bexI)
apply (erule_tac [2] domainI)
apply (rule initseg_appI1)
apply (erule_tac [2] initsegD2)
apply assumption

apply (rule LBindingI)
apply assumption+
apply (rule LBindingI)
apply assumption+

apply (erule initseg_left_appE)
apply assumption
apply simp
apply (clarify elim!: LFO_E LFreeInE2)
(* apply (rename_tac j l''' k) *)
apply (subgoal_tac "ld: list(nat)")
prefer 2
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD1])
apply assumption
apply (rule LOcc_in_Occ_range [THEN Occ_rangeE])
apply assumption
apply (drule_tac l="lc" in DenseTree_CorrectArity_0D)
prefer 2 apply assumption
apply (rule_tac [3] sym [THEN initsegI])
prefer 3 apply assumption
prefer 2 apply hypsubst
apply assumption
apply (drule_tac x="TLVar(x)" in bspec)
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD2])
apply assumption
apply simp
apply (erule initsegD2)
apply assumption
apply hypsubst
apply (erule LOcc_domain [THEN subsetD, THEN SigmaD1])
apply assumption
apply (subgoal_tac "lb = []" "TLVar(y) = TLVar(x)")
apply hypsubst
apply simp
apply hypsubst
apply (erule functionalD)
apply assumption
apply simp
apply (rule app_Nil_eqD1)
apply (erule sym [THEN trans])
apply (erule sym)
apply assumption
done

lemma LBoundBy_LsubstI2:
  assumes major: "LBoundBy(<l, TLVar(y)>, <m, TLLam(y)>, N)"
  and prem: "<n, TLVar(x)>: LFO(x, M)"
  shows "LBoundBy(<n@l, TLVar(y)>, <n@m, TLLam(y)>, Lsubst(M, x, N))"
apply (rule major [THEN LBoundByE2])
apply (erule LBindingE2)
apply (subgoal_tac "n: list(nat)" "M: LTerm"
                   "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N))
                     : Occ_range(LTag, LArity)")
prefer 2
apply (assumption | rule LTerm_Occ_Graft_in_Occ_range2
        LOcc_in_Occ_range Incomparable_LFO
        LFO_subset_LOcc [THEN domain_mono] prem)+
prefer 2
apply (rule prem [THEN LFO_E2])
apply (erule LFreeInE2)
apply assumption
prefer 2
apply (rule prem [THEN LFO_E2])
apply (erule LFreeInE2)
apply (rule LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption

apply (unfold Lgraft_def Lsubst_def)
apply (rule LBoundByI)
apply (erule_tac [2] LBindingE2)
apply (rule LBindingI)
apply (simp_all only: LTerm_def_Occ_Occinv)
apply (erule LTerm_def_Occinv_type)
apply (erule_tac [4] initseg_left_appE)
prefer 4 apply assumption
apply (erule Occ_ShiftI [THEN prem [THEN domainI, THEN Occ_GraftI2]])+
apply (rule initseg_appI2)
apply assumption+
apply hypsubst
apply (rule_tac f="%x. n @ x" in function_apply_eq)
apply (erule spec [THEN mp, THEN mp])
apply assumption
apply (safe elim!: LTag.free_elims LOcc_domain [THEN [2] Occ_GraftE]
           Occ_ShiftE)
apply (erule_tac [4] initseg_left_appE)
apply (subgoal_tac [5] "lc = l")
apply (rule_tac [6] app_right_inj_iff [THEN iffD1, THEN sym])
prefer 7 apply assumption
prefer 6 apply assumption
prefer 4 apply assumption
apply (insert prem)
apply (subgoal_tac [4] "ma: list(nat)" "n = ma")
apply (erule_tac [6] LFO_E)+
apply (erule_tac [6] LFreeInE2)+
apply (rule_tac [6] LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 7 apply blast
prefer 6 apply assumption
apply (erule_tac [5] x="la" in app_appE)
apply (subgoal_tac [8] "initseg(nat, ma, n)")
apply (erule_tac [9] sym [THEN initsegI])
apply (subgoal_tac [7] "initseg(nat, n, ma)")
apply (erule_tac [8] sym [THEN initsegI])
prefer 5 apply assumption
prefer 5 apply assumption
prefer 6 apply assumption
prefer 6 apply assumption
prefer 6 apply assumption
prefer 7 apply assumption
prefer 7 apply assumption
prefer 7 apply assumption
apply (rule_tac [6] Incomparable_LFO [THEN IncomparableD, THEN sym])
apply (erule_tac [8] domainI)
apply (rule_tac [5] Incomparable_LFO [THEN IncomparableD])
apply (erule_tac [7] domainI)
prefer 5 apply assumption
prefer 5 apply assumption
prefer 5 apply (assumption | rule domainI)+
prefer 5 apply assumption
prefer 5 apply assumption
prefer 5 apply (assumption | rule domainI)+
prefer 4 apply hypsubst
apply simp
apply (rule LBindingI)
apply assumption+
apply (erule notE, rule bexI,
       rule_tac [2] prem [THEN domainI],
       erule initseg_appI1, erule initsegD2)+
done

lemma LFreeIn_LsubstE:
  assumes major: "LFreeIn(<l, TLVar(y)>, Lsubst(M, x, N))"
  and M_term: "M: LTerm"
  and N_term: "N: LTerm"
  and prem1:
     "[| LFreeIn(<l, TLVar(y)>, M); x ~= y |] ==> R"
  and prem2:
     "!!n a b. [| l =  n @ a; LFreeIn(<n, TLVar(x)>, M);
         LFreeIn(<a, TLVar(y)>, N);
         ALL m. ~(initseg(nat, m, n) & <m, TLLam(y)>: LOcc(M))|] ==> R"
  shows "R"
apply (insert M_term N_term)
apply (rule major [THEN LFreeInE2])
apply (erule LOcc_LsubstE)
apply (rule_tac [4] prem2)
apply (safe elim!: LFO_E2)
apply (rule_tac [2] refl)
prefer 2 apply assumption
apply (rule_tac [2] LFreeInI2)
apply (erule_tac [4] LBinding_imp_LBoundByE)
apply (drule_tac [4] LBoundBy_LsubstI2)
apply (erule_tac [4] LFO_I)
apply (erule_tac [4] LBoundByD1 [THEN LBindingE2])
apply (rule prem1)
apply (rule LFreeInI2)
apply (erule_tac [3] LBinding_imp_LBoundByE)
apply (drule_tac [3] N="N" and x="x" in LBoundBy_LsubstI1)
apply (erule_tac [4] LBoundByD1 [THEN LBindingE2])
prefer 6
prefer 7
apply assumption+

apply (rule_tac [2] notI)
prefer 2
apply hypsubst
apply (erule notE)
apply (rule LFreeInI [THEN LFO_I])
apply (erule_tac [3] spec [THEN mp, THEN notE])
apply (rule_tac [3] LOcc_LsubstI1)
prefer 7 apply assumption
apply (safe elim!: LTag.free_elims LFO_E)

apply (erule_tac [3] spec [THEN mp, THEN notE])
apply (erule_tac [2] spec [THEN mp, THEN notE])
apply (erule_tac [1] spec [THEN mp, THEN notE])
apply assumption+
apply (rule LOcc_LsubstI1)
prefer 2 apply assumption
apply (erule_tac [4] initseg_trans)
apply (rule_tac [4] initseg_appI1)
apply (erule_tac [5] LOcc_typeD1)
apply (erule_tac [4] LFreeInE2)
apply (erule_tac [4] LOcc_typeD1)
apply (safe elim!: LTag.free_elims LFO_E)
done

lemma LFreeIn_LsubstI1:
  assumes major: "LFreeIn(<l, TLVar(y)>, M)"
  and sub: "LFreeForIn(N, x, M)"
  and prem: "x ~= y"
  shows "LFreeIn(<l, TLVar(y)>, Lsubst(M, x, N))"
apply (rule sub [THEN LFreeForInE])
apply (subgoal_tac "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N))
                        : Occ_range(LTag, LArity)")
prefer 2
apply (assumption | rule LTerm_Occ_Graft_in_Occ_range2
        LOcc_in_Occ_range Incomparable_LFO
        LFO_subset_LOcc [THEN domain_mono])+
apply (rule major [THEN LFreeInE2])
apply (rule LFreeInI2)
apply (erule_tac [3] LBinding_imp_LBoundByE)
apply (erule_tac [3] LBoundBy_LsubstE)
apply (rule_tac [3] sub)
apply (unfold Lsubst_def)
apply (rule LTerm_def_graft_type)
apply (assumption | rule Incomparable_LFO domain_mono
          LFO_subset_LOcc)+
apply (unfold Lgraft_def)
apply (simp_all only: LTerm_def_Occ_Occinv)
apply (rule Occ_GraftI1)
apply assumption
apply (rule notI)
apply (insert prem)
apply (safe elim!: LFO_E LFreeInE LTag.free_elims)
apply (erule_tac M1="M" in  LOcc_in_Occ_range [THEN Occ_rangeE])
apply (drule DenseTree_CorrectArity_0D)
prefer 4 apply assumption
prefer 2 apply assumption
prefer 2 apply assumption
apply (drule_tac x="TLVar(x)" in bspec)
apply (erule_tac LTag.intros)
apply simp
apply hypsubst
apply (subgoal_tac "TLVar(x) = TLVar(y)")
prefer 2
apply (erule functionalD)
apply assumption+
apply (rule prem [THEN notE])
apply simp
apply (erule_tac [2] LBoundByD1 [THEN LBindingE2])
apply (erule_tac [1] LBoundByD1 [THEN LBindingE2])
apply (erule spec [THEN mp, THEN notE])
apply assumption+
apply (subgoal_tac "lb: list(nat)")
apply (erule_tac M1="M" in LOcc_in_Occ_range [THEN Occ_rangeE])
apply (drule DenseTree_CorrectArity_0D)
apply (rule_tac [4] initseg_appI1)
prefer 3 apply assumption
prefer 2 apply assumption
apply (erule_tac [3] initsegD2)
prefer 2 apply assumption
apply (drule_tac x="TLVar(x)" in bspec)
apply (erule LTag.intros)
apply simp
apply (drule sym [THEN app_Nil_eqD1])
apply assumption
apply hypsubst
apply (erule initseg_NilE)
apply hypsubst
apply (subgoal_tac "TLLam(y) = TLVar(y)")
apply (blast elim!: LTag.free_elims)
apply (erule_tac M2="N" in LOcc_in_Occ_range [THEN Occ_range_functionalD,
        THEN functionalD])
apply assumption+
apply (rule LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption
done

lemma LFreeIn_LsubstI2:
  assumes major: "LFreeIn(<l, TLVar(y)>, N)"
  and sub: "LFreeForIn(N, x, M)"
  and prem: "<n, TLVar(x)>: LFO(x, M)"
  shows "LFreeIn(<n @ l, TLVar(y)>, Lsubst(M, x, N))"
apply (rule sub [THEN LFreeForInE])
apply (subgoal_tac "n: list(nat)"
                    "Occ_Graft(LOcc(M), domain(LFO(x, M)), LOcc(N)):
                         Occ_range(LTag, LArity)")
prefer 2
apply (assumption | rule LTerm_Occ_Graft_in_Occ_range2
        LOcc_in_Occ_range Incomparable_LFO
        LFO_subset_LOcc [THEN domain_mono])+
apply (rule major [THEN LFreeInE2])
apply (rule LFreeInI2)
apply (erule_tac [3] LBinding_imp_LBoundByE)
apply (erule_tac [3] LBoundBy_LsubstE)
apply (rule_tac [3] sub)
apply (unfold Lsubst_def)
apply (rule LTerm_def_graft_type)
apply (assumption | rule Incomparable_LFO domain_mono LFO_subset_LOcc)+
apply (unfold Lgraft_def)
apply (simp_all only: LTerm_def_Occ_Occinv)
apply (rule Occ_GraftI2)
apply (erule_tac [2] Occ_ShiftI)
apply (rule prem [THEN domainI])
apply (rule prem [THEN LFO_E2])
apply (erule LBoundByD1 [THEN LBindingE2])
apply (erule LFreeInE2)

apply (rule LOcc_in_Occ_range [THEN Occ_rangeE])
apply (drule_tac [2] DenseTree_CorrectArity_0D)
apply (rule_tac [5] initseg_appI1)
prefer 4 apply assumption
prefer 3 apply assumption
apply (drule_tac [2] x="TLVar(x)" in bspec)
apply (erule_tac [2] LTag.intros)
prefer 2 apply simp
apply (rule_tac [3] LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 4 apply assumption
apply assumption+
apply (drule_tac sym [THEN app_Nil_eqD1])
apply assumption
apply hypsubst
apply (simp only: app_right_Nil)
apply (subgoal_tac "TLVar(y) = TLVar(x)")
prefer 2
apply (erule_tac functionalD)
apply assumption+
apply (erule_tac P5="%m. initseg(nat, m, n)" in
        spec [THEN mp, THEN notE])
prefer 2 apply assumption
apply simp

apply (erule LBoundByD1 [THEN LBindingE2])
apply (insert prem)
apply (subgoal_tac "na: list(nat)" "na = n")
apply (erule_tac [2] app_appE)
prefer 2 apply assumption
prefer 2 apply assumption
apply (rule_tac [3] Incomparable_LFO [THEN IncomparableD])
apply (erule_tac [4] sym [THEN initsegI])
apply (rule_tac [2] Incomparable_LFO [THEN IncomparableD, THEN sym])
apply (erule_tac [3] sym [THEN initsegI])
apply (simp only: app_right_inj_iff)
apply (assumption | rule domainI)+
apply (erule_tac [2] LFO_E2 LFreeInE2)+
apply (erule_tac [1] LFO_E2 LFreeInE2)+
apply (rule LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption
apply (rule LOcc_domain [THEN subsetD, THEN SigmaD1])
prefer 2 apply assumption
apply assumption
done

lemma LFreeForIn_lemma:
  assumes major:
     "!!y l m. [| LFreeIn(<l, TLVar(y)>, N); LFreeIn(<m, TLVar(x)>, M) |]
          ==> LFreeIn(<m @ l, TLVar(y)>, Lsubst(M, x, N))"
  shows
  "[|
      N: LTerm; x: LVariable; M: LTerm
   |] ==> LFreeForIn(N, x, M)"
apply (rule LFreeForInI)
apply assumption+
apply (erule LFV_E)
apply (frule major)
apply assumption
apply (erule_tac l="l @ la" in LFreeInE2)
apply (safe elim!: LTag.free_elims LOcc_LsubstE LFO_E2)
apply (erule LFreeInE2)+
apply (erule_tac x1="x" in TLVar_leaf [THEN conjE])
apply (rule_tac [2] initseg_appI1)
apply assumption
apply (erule initsegD2)
apply (drule initsegD2)
apply (drule LOcc_typeD1, erule_tac [2] app_typeD)
apply assumption+
apply (blast elim!: LTag.free_elims)
apply (erule app_appE)
apply (erule initsegD2)
apply (erule LFreeInE2, erule LOcc_typeD1)
apply assumption
apply (safe elim!: LFreeInE2)
apply (rule_tac [2] M1="M" in TLVar_leaf [THEN conjE])
apply (rule_tac [4] initseg_appI1)
prefer 3 apply assumption
prefer 2 apply assumption
apply (drule_tac [5] app_Nil_eqD1)
prefer 2 apply (erule LOcc_typeD1, assumption)
prefer 2 apply assumption
prefer 2 apply assumption
prefer 2 apply (erule LOcc_typeD1, assumption)

prefer 2
apply hypsubst
apply (erule spec [THEN mp, THEN notE], rule LOcc_LsubstI1)
prefer 2 apply assumption
apply (erule_tac [4] initseg_appI3)
apply (drule_tac [4] LOcc_typeD1, erule_tac [5] app_typeD)
apply (rule_tac [5] list.intros)
apply (safe elim!: LFO_E LTag.free_elims)
apply (rule_tac M1="M" in TLVar_leaf [THEN conjE])
apply (rule_tac [3] initseg_appI1)
prefer 2 apply assumption
apply assumption
apply (drule_tac [4] app_Nil_eqD1)
prefer 2 apply assumption
prefer 2 apply assumption
prefer 2 apply (erule LOcc_typeD1, assumption)
apply (erule_tac initsegD2)
apply hypsubst
apply (erule spec [THEN mp, THEN notE], rule LOcc_LsubstI1)
prefer 2 apply assumption
apply (erule_tac [4] initseg_appI3)
apply (erule_tac [4] LOcc_typeD1)
apply (safe elim!: LFO_E LTag.free_elims)
done

lemma Lsubst_lemma:
  assumes major: "LFreeForIn(A, x, M)"
  shows
    "[| x ~: LFV(B); y ~= x;
        M: LTerm; A: LTerm; B: LTerm |]
       ==> Lsubst(Lsubst(M, x, A), y, B) =
                Lsubst(Lsubst(M, y, B), x, Lsubst(A, y, B))"
apply (subgoal_tac "x ~= y")
prefer 2 apply blast
apply (rule major [THEN rev_mp])
apply (erule_tac x="M" in LTerm.induct)
prefer 3
apply (rule impI)
apply (erule_tac LFreeForIn_LTermEs)
apply simp

prefer 2
apply (rule impI)
apply (erule_tac LFreeForIn_LTermEs)
apply simp
apply (case_tac "y = xa")
apply hypsubst
apply simp
apply simp
apply (case_tac "y = xa")
apply simp
apply simp

prefer 2
apply (rule impI)
apply (erule_tac LFreeForIn_LTermEs)
apply (case_tac "y = xa")
apply hypsubst
apply simp
apply simp

apply (case_tac "x = xa")
apply (subgoal_tac [3] "x ~: LFV(Lsubst(M, y, B))") 
apply hypsubst
apply simp_all
apply (rule notI)
apply (erule LFV_E)
apply (erule LFreeIn_LsubstE)
apply assumption+
apply (erule notE, erule LFV_I)+
done

lemma Lsubst_lemma2:
  assumes major: "LFreeForIn(LVar(x), y, M)"
  and sub: "x ~: LFV(M)"
  and prem: "N: LTerm"
  shows "Lsubst(Lsubst(M, y, LVar(x)), x, N) = Lsubst(M, y, N)"
apply (subgoal_tac "M: LTerm" "x: LVariable" "y: LVariable")
defer 1
apply (rule major [THEN LFreeForInE],
       erule LTerm_typeEs,
       assumption)+
apply (insert prem)
apply (rule sub [THEN rev_mp])
apply (rule major [THEN rev_mp])
apply (erule_tac x="M" in LTerm.induct)
apply simp_all
apply (safe elim!: LFreeForIn_LTermEs)
apply (erule_tac [6] notE)
apply (erule_tac [7] notE)
apply (erule_tac [8] notE)
apply simp_all
apply (case_tac "y = xa")
apply (subgoal_tac [3] "x ~= xa")
apply simp_all
apply blast
done

lemma Lsubst_lemma3:
  "[| M: LTerm; A: LTerm; B: LTerm; y ~: LFV(A); x ~: LFV(B); x ~= y |] ==>
     Lsubst(Lsubst(M, x, A), y, B) =
            Lsubst(Lsubst(M, y, B), x, A)"
apply (erule_tac x="M" in LTerm.induct)
apply (case_tac [2] "x = xa")
apply (case_tac [3] "y = xa")
apply (case_tac [2] "y = xa")
apply (case_tac [1] "x = xa")
apply (case_tac [2] "y = xa")
apply (case_tac [1] "y = xa")
apply simp_all
done

lemma Lsubst_lemma4:
  assumes sub: "y ~: LFV(M) - {x}"
  and prem: "LFreeForIn(A, x, M)"
  shows "B: LTerm ==> 
     Lsubst(Lsubst(M, x, A), y, B) = Lsubst(M, x, Lsubst(A, y, B))"
apply (insert prem [THEN LFreeForInD1])
apply (rule sub [THEN rev_mp])
apply (rule prem [THEN rev_mp])
apply (rule prem [THEN LFreeForInD3, THEN LTerm.induct])
apply (case_tac [2] "x = xa")
apply (case_tac [1] "x = xa")
apply simp_all
apply (safe elim!: LFreeForIn_LTermEs)
apply simp_all
apply (case_tac "y = xa")
apply simp_all
done

end
