(*
    File:        OccTools.thy
    Time-stamp:  <2020-06-22T03:53:40Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory OccTools imports ZF_aux InitSeg FinBnd begin

definition list_op :: "[i, i] => i" where
"list_op(A, X) == {z: univ(A). z = [] | (EX a l. z = Cons(a, l) &
                         a: A & l: X)}"

definition list_dom :: "i=>i" where
"list_dom(A) == univ(A)"


definition Occ_fbs_dom :: "i=>i" where
"Occ_fbs_dom(Tag) == list_dom(nat) * Tag"

definition Occ_fbs_op :: "[i, i] => i" where
"Occ_fbs_op(Tag, X) == list_op(nat, domain(X)) * Tag"


definition Occ_shift :: "[i, i] => i" where
"Occ_shift(b, X) == {z. y: X, EX l T. z = <Cons(b, l), T> & y = <l, T>}"

definition Occ_subtree :: "[i, i] => i" where
"Occ_subtree(b, X) == {z. y: X, EX l T. z = <l, T> & y = <Cons(b, l), T>}"

definition Occ_primary :: "i=>i" where
"Occ_primary(X) == {z: X. EX T.  z = <[], T>}"

definition Occ_cons :: "[i, i]=>i" where
"Occ_cons(T, l) == {<[], T>} Un (UN z: length(l). Occ_shift(z, nth(z, l)))"


definition functional :: "i=>o" where
"functional(X) == ALL l A B. <l, A>: X & <l, B>: X --> A = B"

definition CorrectArity :: "[i, i, i]=>o" where
"CorrectArity(X, T, n) == ALL l. <l, T>: X -->
                    (ALL m. m < n -->  (EX N. <l@[m], N>: X)) &
                    (ALL m. n \<le> m --> ~(EX N. <l@[m], N>: X))"

definition DenseTree :: "i=>o" where
"DenseTree(X) == (ALL l A m. <l, A>: X & initseg(nat, m, l) -->
                                 (EX B. <m, B>: X))"


definition Occ_range :: "[i, i=>i]=>i" where
"Occ_range(Tag, Arity) ==
         {X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)).
             X ~= 0 & functional(X) & DenseTree(X) &
             (ALL T: Tag. CorrectArity(X, T, Arity(T)))}"


definition Occ_cons_cond :: "[i, i=>i, i, i=>i] =>o" where
"Occ_cons_cond(Terms, Occ, Tag, Arity) ==
   (ALL T: Tag. Arity(T): nat) &
   (ALL T: Tag. ALL l: list(Pow(list(nat)*Tag)). Arity(T) = length(l) &
      (ALL z: length(l). EX N: Terms. nth(z, l) = Occ(N))
      --> (EX M: Terms. Occ(M) = Occ_cons(T, l)))"

definition Occ_ind_cond :: "[i, i=>i, i, i=>i, [i, i]=>i] =>o" where
"Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons) ==
   (ALL P.
     (ALL T: Tag. ALL l: list(Terms).
          Term_cons(T, l): Terms &
          Arity(T) = length(l) &
          Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l)) &
          (ALL z: length(l). nth(z, l): P)
         --> Term_cons(T, l): P
      ) --> (ALL M: Terms. M: P))"


lemma Prod_domain_0_eq:
    "domain(0)*A = 0"
apply (rule domain_0 [THEN ssubst])
apply (rule Sigma_empty1)
done

lemma list_op_bnd_mono:
  "bnd_mono(list_dom(A), list_op(A))"
apply (unfold bnd_mono_def list_dom_def list_op_def)
apply (rule list.bnd_mono [unfolded bnd_mono_def])
done

lemma list_op_lfp_eq:
  "list(A) = lfp(list_dom(A), list_op(A))"
apply (unfold list.defs list_dom_def list_op_def lfp_def)
apply (rule refl)
done

lemma list_op_continuous:
  "X~= 0 ==> list_op(A, Union(X)) = (UN x: X. list_op(A, x))"
apply (unfold list_op_def)
apply (erule not_emptyE)
apply (rule equalityI)
apply blast+
done

(** Occ_shift **)
lemma Occ_shiftI:
  "<l, T>: X ==> <Cons(b, l), T>: Occ_shift(b, X)"
apply (unfold Occ_shift_def)
apply blast
done

lemma Occ_shiftE:
  "[| x: Occ_shift(b, X); 
      !!l T. [| x = <Cons(b, l), T>; <l, T>: X |] ==> R
   |] ==> R"
apply (unfold Occ_shift_def)
apply blast
done

lemma Occ_shiftE2:
  "[| <l, T>: Occ_shift(b, X);
      !!m. [| l = Cons(b, m); <m, T>: X |] ==> R |] ==> R"
apply (unfold Occ_shift_def)
apply blast
done

lemma Occ_shift_0:
  "Occ_shift(b, 0) = 0"
apply (unfold Occ_shift_def)
apply blast
done

lemma Occ_shift_cons:
  "Occ_shift(b, cons(<l, T>, X)) = cons(<Cons(b, l), T>, Occ_shift(b, X))"
apply (unfold Occ_shift_def)
apply (rule equalityI)
apply blast+
done

lemma Occ_shift_continuous:
  "Occ_shift(b, Union(X)) = (UN x: X. Occ_shift(b, x))"
apply (unfold Occ_shift_def)
apply (rule equalityI)
apply blast+
done

lemma Occ_shift_Un:
  "Occ_shift(b, X Un Y) = Occ_shift(b, X) Un Occ_shift(b, Y)"
apply (unfold Occ_shift_def)
apply (rule equalityI)
apply blast+
done

lemma Occ_shift_iff:
  assumes domX: "X <= A*B"
  and domY: "Y <= C*D"
  and not_emptyX: "X ~= 0"
  shows "Occ_shift(a, X) = Occ_shift(b, Y) <-> a = b & X = Y"
apply (rule iffI)
apply (rule conjI)
apply (drule equalityD1)
apply (rule not_emptyX [THEN not_emptyE])
apply (frule domX [THEN subsetD])
apply (erule SigmaE)
apply hypsubst
apply (drule subsetD)
apply (erule Occ_shiftI)
apply (erule Occ_shiftE2)
apply (erule Cons_iff [THEN iffD1, THEN conjunct1])
apply (rule equalityI)
apply (drule_tac [2] equalityD2)
apply (drule_tac [1] equalityD1)

apply (rule subsetI)
apply (frule domX [THEN subsetD] domY [THEN subsetD])
apply (erule SigmaE)
apply hypsubst
apply (drule subsetD)
apply (erule Occ_shiftI)
apply (erule Occ_shiftE2)
apply (drule Cons_iff [THEN iffD1, THEN conjunct2])
apply hypsubst
apply assumption

apply (rule subsetI)
apply (frule domX [THEN subsetD] domY [THEN subsetD])
apply (erule SigmaE)
apply hypsubst
apply (drule subsetD)
apply (erule Occ_shiftI)
apply (erule Occ_shiftE2)
apply (drule Cons_iff [THEN iffD1, THEN conjunct2])
apply hypsubst
apply assumption

apply (erule conjE)
apply hypsubst
apply (rule refl)
done

lemmas Occ_shift_simps = 
    Occ_shift_0 Occ_shift_cons Occ_shift_Un Occ_shift_iff


(** Occ_subtree **)

lemma Occ_subtreeI:
  "<Cons(b, l), T>: X ==> <l, T>: Occ_subtree(b, X)"
apply (unfold Occ_subtree_def)
apply (rule ReplaceI)
prefer 2 apply assumption
apply (rule refl conjI exI)+
apply (elim exE conjE)
apply simp
done

lemma Occ_subtreeD:
  "<l, T>: Occ_subtree(b, X) ==> <Cons(b, l), T>: X"
apply (unfold Occ_subtree_def)
apply blast
done

lemma Occ_subtreeE:
  "[| x: Occ_subtree(b, X);
      !!l T. [| x = <l, T>; <Cons(b, l), T>: X |] ==> R |] ==> R"
apply (unfold Occ_subtree_def)
apply blast
done

lemma Occ_subtreeE2:
  "[| <l, T>: Occ_subtree(b, X);
      <Cons(b, l), T>: X ==> R |] ==> R"
apply (unfold Occ_subtree_def)
apply blast
done

lemma Occ_subtree_0:
  "Occ_subtree(b, 0) = 0"
apply (unfold Occ_subtree_def)
apply blast
done

lemma Occ_subtree_cons_Nil:
  "Occ_subtree(a, cons(<[], T>, X)) = Occ_subtree(a, X)"
apply (unfold Occ_subtree_def)
apply (rule equalityI)
apply clarify
apply (erule consE)
apply simp
apply (rule ReplaceI)
apply (intro exI conjI)
prefer 2 apply (rule refl)
apply (rule refl)
apply assumption
apply (elim exE conjE)
apply simp
apply (rule subsetI)
apply clarify
apply (rule ReplaceI)
prefer 2 apply (rule consI2, assumption)
apply blast
apply (elim exE conjE)
apply simp
done

lemma Occ_subtree_cons_Cons:
  "Occ_subtree(a, cons(<Cons(b, l), T>, X)) =
           if(a = b, cons(<l, T>, Occ_subtree(b, X)), Occ_subtree(a, X))"
apply (case_tac "a = b")
apply (rule if_P [THEN sym, THEN [2] trans])
prefer 2 apply assumption
apply (rule_tac [2] if_not_P [THEN sym, THEN [2] trans])
prefer 3 apply assumption
apply (rule_tac [2] equalityI)
apply (rule equalityI)
apply (blast intro!: Occ_subtreeI elim!: Occ_subtreeE
          dest!: Cons_iff [THEN iffD1])+
done

lemma Occ_subtree_continuous:
  "Occ_subtree(b, Union(X)) = (UN x: X. Occ_subtree(b, x))"
apply (rule equalityI)
apply (blast intro!: Occ_subtreeI elim!: Occ_subtreeE
          dest!: Cons_iff [THEN iffD1])+
done

lemma Occ_subtree_UN:
  "Occ_subtree(b, UN z: A. f(z)) = (UN z: A. Occ_subtree(b, f(z)))"
apply (rule equalityI)
apply (blast intro!: Occ_subtreeI elim!: Occ_subtreeE
          dest!: Cons_iff [THEN iffD1])+
done

lemma Occ_subtree_Un:
  "Occ_subtree(b, X Un Y) = Occ_subtree(b, X) Un Occ_subtree(b, Y)"
apply (rule equalityI)
apply (blast intro!: Occ_subtreeI elim!: Occ_subtreeE
          dest!: Cons_iff [THEN iffD1])+
done

lemma Occ_subtree_shift:
  assumes prem: "X <= A*B"
  shows "Occ_subtree(a, Occ_shift(b, X)) = if(a = b, X, 0)"
apply (case_tac "a = b")
apply simp_all
prefer 2
apply (rule subset_empty_iff [THEN iffD1])
apply (rule subsetI)
apply (erule notE)
apply (blast intro!: Occ_subtreeI Occ_shiftI
        elim!: Occ_subtreeE Occ_shiftE dest!: Cons_iff [THEN iffD1])
apply (rule equalityI)
apply (blast intro!: Occ_subtreeI Occ_shiftI
        elim!: Occ_subtreeE Occ_shiftE dest!: Cons_iff [THEN iffD1])
apply (rule subsetI)
apply (frule prem [THEN subsetD])
apply (erule SigmaE)
apply hypsubst
apply (blast intro!: Occ_subtreeI Occ_shiftI
        elim!: Occ_subtreeE Occ_shiftE dest!: Cons_iff [THEN iffD1])
done

lemmas Occ_subtree_simps = Occ_subtree_0 Occ_subtree_cons_Nil
                        Occ_subtree_cons_Cons Occ_subtree_Un
                        Occ_subtree_UN Occ_subtree_shift

(** Occ_primary **)
lemma Occ_primaryI:
  "<[], T>: X ==> <[], T>: Occ_primary(X)"
apply (unfold Occ_primary_def)
apply blast
done

lemma Occ_primaryE:
  "[| x: Occ_primary(X);
      !!T. [| x = <[], T>; <[], T>: X |] ==> R |] ==> R"
apply (unfold Occ_primary_def)
apply blast
done

lemma Occ_primaryE2:
  "[| <l, T>: Occ_primary(X);
      !!T. [| l = []; <[], T>: X |] ==> R |] ==> R"
apply (unfold Occ_primary_def)
apply blast
done

lemma Occ_primary_0:
  "Occ_primary(0) = 0"
apply (unfold Occ_primary_def)
apply blast
done

lemma Occ_primary_cons:
  "Occ_primary(cons(<l, T>, X)) =
           if(l = [], cons(<[], T>, Occ_primary(X)), Occ_primary(X))"
apply (case_tac "l = []")
apply simp_all
apply (rule_tac [2] equalityI)
apply (rule equalityI)
apply (blast intro!: Occ_primaryI elim!: Occ_primaryE)+
done

lemma Occ_primary_continuous:
  "Occ_primary(Union(X)) = (UN x: X. Occ_primary(x))"
apply (rule equalityI)
apply (blast intro!: Occ_primaryI elim!: Occ_primaryE)+
done

lemma Occ_primary_UN:
  "Occ_primary(UN z: X. f(z)) = (UN z: X. Occ_primary(f(z)))"
apply (rule equalityI)
apply (blast intro!: Occ_primaryI elim!: Occ_primaryE)+
done

lemma Occ_primary_Un:
  "Occ_primary(X Un Y) = Occ_primary(X) Un Occ_primary(Y)"
apply (rule equalityI)
apply (blast intro!: Occ_primaryI elim!: Occ_primaryE)+
done

lemma Occ_primary_idempotent:
  "Occ_primary(Occ_primary(X)) = Occ_primary(X)"
apply (rule equalityI)
apply (blast intro!: Occ_primaryI elim!: Occ_primaryE)+
done

lemma Occ_primary_shift:
  "Occ_primary(Occ_shift(b, X)) = 0"
apply (rule subset_empty_iff [THEN iffD1])
apply (rule subsetI)
apply (clarify elim!: Occ_primaryE Occ_shiftE)
apply simp
done

lemma Occ_primary_subtree_shift_eq:
  assumes prem: "X <= list(A) * B"
  shows "X = Occ_primary(X) Un (UN z: A. Occ_shift(z, Occ_subtree(z, X)))"
apply (rule equalityI)
apply (rule subsetI)
apply (frule prem [THEN subsetD])
apply (erule SigmaE)
apply hypsubst
apply (erule list.cases)
apply simp_all
apply (blast intro!: Occ_subtreeI Occ_shiftI Occ_primaryI
        elim!: Occ_subtreeE Occ_shiftE Occ_primaryE
        dest!: Cons_iff [THEN iffD1])+
done

lemmas Occ_primary_simps = 
     Occ_primary_0 Occ_primary_cons 
     Occ_primary_Un Occ_primary_UN
     Occ_primary_shift Occ_primary_idempotent


(** Occ_cons **)
lemma Occ_consI1:
  "<[], T>: Occ_cons(T, l)"
apply (unfold Occ_cons_def)
apply blast
done

lemma Occ_consI2:
  "[| a: length(l); <m, U>: nth(a, l) |] ==>
           <Cons(a, m), U>: Occ_cons(T, l)"
apply (unfold Occ_cons_def)
apply (rule UnI2)
apply (erule UN_I)
apply (erule Occ_shiftI)
done

lemma Occ_consE:
  assumes major: "x: Occ_cons(T, l)"
  and "x = <[], T> ==> R"
  and "!! a m U. [| x = <Cons(a, m), U>; a: length(l);
              <m, U>: nth(a, l) |] ==> R"
  shows "R"
apply (rule major [unfolded Occ_cons_def, THEN UnE])
apply (erule singletonE)
apply (erule assms)
apply (erule UN_E)
apply (erule Occ_shiftE)
apply (erule assms)
apply assumption+
done

lemma Occ_cons_ConsE:
  assumes major: "<Cons(a, m), U>: Occ_cons(T, l)"
  and prem: "[| a: length(l); <m, U>: nth(a, l) |] ==> R"
  shows "R"
apply (rule major [THEN Occ_consE])
apply simp
apply (rule prem)
apply simp_all
done

lemma Occ_consE2:
  assumes major: "x: Occ_cons(T, l)"
  and l_list: "l: list(A)"
  and "x = <[], T> ==> R"
  and "!! a m U. [| x = <Cons(a, m), U>; a < length(l);
                   <m, U>: nth(a, l) |] ==> R"
  shows "R"
apply (rule major [unfolded Occ_cons_def, THEN UnE])
apply (erule singletonE)
apply (erule assms)
apply (erule UN_E)
apply (erule Occ_shiftE)
apply (erule assms)
apply (erule l_list [THEN length_type, THEN nat_into_Ord, THEN [2] ltI])
apply assumption
done

lemma Occ_cons_type:
  assumes prem1: "T: B"
  and prem2: "l: list(Pow(list(nat)* B))"
  shows "Occ_cons(T, l) <= list(nat) * B"
apply (rule subsetI)
apply (erule Occ_consE)
apply hypsubst
apply (rule SigmaI)
apply (rule list.intros)
apply (rule prem1)
apply hypsubst
apply (frule prem2 [THEN length_type, THEN [2] mem_nat_in_nat])
apply (frule prem2 [THEN [2] nth_type1])
apply (simp add: Pow_Un_0_simps)
apply blast
done

lemma Occ_cons_type2:
  assumes prem1: "T: B"
  and prem2: "length(l): nat"
  and prem3: "ALL z: length(l). nth(z, l)<=list(nat)*B"
  shows "Occ_cons(T, l) <= list(nat) * B"
apply (rule subsetI)
apply (erule Occ_consE)
apply hypsubst
apply (rule SigmaI)
apply (rule list.intros)
apply (rule prem1)
apply hypsubst
apply (frule prem2 [THEN [2] mem_nat_in_nat])
apply (drule prem3 [THEN bspec])
apply blast
done

lemma Occ_cons_Nil:
  "Occ_cons(T, []) = {<[], T>}"
apply (rule equalityI)
apply (rule subsetI)
apply (erule Occ_consE)
apply simp_all
apply (blast intro!: Occ_consI1)
done

lemma Occ_cons_app_last:
  "l: list(A) ==> Occ_cons(T, l@[X]) =
                  Occ_cons(T, l) Un Occ_shift(length(l), X)"
apply (subgoal_tac "l: list(A Un {X})")
apply (simp add: Occ_cons_def Un_commute)
apply (rule list_mono [THEN subsetD])
apply (rule Un_upper1)
apply assumption
done

lemma Occ_subtree_Occ_cons:
  "[| b: nat; l: list(Pow(A * B)) |] ==>
            Occ_subtree(b, Occ_cons(T, l)) = nth(b, l)"
apply (unfold Occ_cons_def)
apply (simp add: Occ_subtree_simps)
apply (rule equalityI)
prefer 2
apply (rule_tac i="b" and j="length(l)" in Ord_linear2)
apply (erule nat_into_Ord)
apply (erule length_type [THEN nat_into_Ord])
apply (safe elim!: Occ_subtreeE Occ_shiftE
            dest!: Cons_iff [THEN iffD1])
prefer 2 apply (frule nth_over_length_lemma)
prefer 2 apply assumption
apply assumption
apply simp
apply (rule UN_I)
apply (erule ltD)
apply (frule nth_type2)
apply assumption
apply (simp add: Occ_subtree_simps)
done

lemma Occ_primary_Occ_cons:
  "Occ_primary(Occ_cons(T, l)) = {<[], T>}"
apply (unfold Occ_cons_def)
apply (simp add: Occ_primary_simps)
done

lemma Occ_cons_iff:
  assumes l_list: "l: list(Pow(A * B))"
  and m_list: "m: list(Pow(A * B))"
  shows "Occ_cons(T, l) = Occ_cons(U, m) <-> T = U &
          (ALL n: length(l) Un length(m). nth(n, l) = nth(n, m))"
apply (safe intro!: nat_UnI length_type)
apply (drule_tac f="Occ_primary" in function_apply_eq)
apply (simp add: Occ_primary_Occ_cons)
apply (drule_tac [2] m_list [THEN length_type, THEN [2] mem_nat_in_nat])
apply (drule l_list [THEN length_type, THEN [2] mem_nat_in_nat])
apply (insert m_list l_list)
apply (drule_tac f="Occ_subtree(n)" in function_apply_eq)
apply (simp add: Occ_subtree_Occ_cons)
apply (drule_tac f="Occ_subtree(n)" in function_apply_eq)
apply (simp add: Occ_subtree_Occ_cons)
apply (unfold Occ_cons_def)
apply (rule equalityI)
apply safe
apply simp_all

apply (case_tac "z < length(m)")
apply (erule bspec [THEN notE])
apply (erule ltD, assumption)
apply (drule not_lt_imp_le)
apply (erule l_list [THEN length_type, THEN [2] mem_nat_in_nat,
                     THEN nat_into_Ord])
apply (rule m_list [THEN length_type, THEN nat_into_Ord])
apply (frule_tac xs="m" in nth_over_length_lemma)
prefer 2 apply assumption
apply (erule length_type [THEN [2] mem_nat_in_nat])
apply assumption
apply (simp add: Occ_shift_0)

apply (case_tac "z < length(l)")
apply (erule bspec [THEN notE])
apply (erule ltD, assumption)
apply (drule not_lt_imp_le)
apply (erule m_list [THEN length_type, THEN [2] mem_nat_in_nat,
                     THEN nat_into_Ord])
apply (rule l_list [THEN length_type, THEN nat_into_Ord])
apply (frule_tac xs="l" in nth_over_length_lemma)
prefer 2 apply assumption
apply (erule length_type [THEN [2] mem_nat_in_nat])
apply assumption
apply (simp add: Occ_shift_0)

done

lemmas Occ_cons_simps = nat_succ_Un  Occ_cons_iff
            Occ_subtree_Occ_cons Occ_primary_Occ_cons


(** functional **)
lemma functionalI:
  "[| !!l A B. [| <l, A>: X; <l, B>: X |] ==> A = B |] ==> functional(X)"
apply (unfold functional_def)
apply blast
done

lemma functionalD:
  "[| functional(X); <l, A>: X; <l, B>: X |] ==> A = B"
apply (unfold functional_def)
apply blast
done


(** DenseTree **)
lemma DenseTreeI:
  "[| !!l A m. [| <l, A>: X; initseg(nat, m, l) |] ==> (EX B. <m, B>: X) |]
      ==> DenseTree(X)"
apply (unfold DenseTree_def)
apply blast
done

lemma DenseTreeE:
  "[| DenseTree(X);
      <l, A>: X; initseg(nat, m, l);
      !!B. [| <m, B>: X |] ==> R |] ==> R"
apply (unfold DenseTree_def)
apply blast
done

lemma CorrectArityI:
  "[| !!l m. [| <l, T>: X; m < n |] ==> (EX N. <l @ [m], N> : X);
      !!l m. [| <l, T>: X; n \<le> m; (EX N. <l @ [m], N> : X) |] ==> False
   |] ==> CorrectArity(X, T, n)"
apply (unfold CorrectArity_def)
apply blast
done

lemma CorrectArityD1:
  "[| CorrectArity(X, T, n);
     <l, T>: X; m < n |] ==>  (EX N. <l @ [m], N>: X)"
apply (unfold CorrectArity_def)
apply blast
done

lemma CorrectArityD2:
  "[| CorrectArity(X, T, n);
     <l, T>: X; n \<le> m |] ==> ~(EX N. <l @ [m], N>: X)"
apply (unfold CorrectArity_def)
apply blast
done

lemma CorrectArityE:
  assumes major: "CorrectArity(X, T, n)"
  and case1: "!!N. [| m < n; <l @ [m], N>: X |] ==> R"
  and case2: "n \<le> m ==> EX N. <l @ [m], N>: X"
  shows "[| <l, T>: X; m: nat; n: nat |] ==> R"
apply (rule Ord_linear2)
apply (frule_tac [4] case2)
apply (rule_tac [4] major [THEN CorrectArityD2, THEN notE])
apply (rule_tac [3] major [THEN CorrectArityD1, THEN exE])
apply (rule_tac [5] case1)
apply (assumption | rule nat_into_Ord)+
done


(** Occ_range **)
lemma Occ_rangeE:
  "[| X: Occ_range(Tag, Arity);
      [| X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag));
         X ~= 0; functional(X); DenseTree(X);
         ALL T: Tag. CorrectArity(X, T, Arity(T)) |] ==> R
   |] ==> R"
apply (unfold Occ_range_def)
apply blast
done

lemma Occ_rangeI:
  "[| X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag));
      X ~= 0; functional(X); DenseTree(X);
      ALL T: Tag. CorrectArity(X, T, Arity(T))
   |] ==> X: Occ_range(Tag, Arity)"
apply (unfold Occ_range_def)
apply blast
done

lemma Occ_range_DenseTreeD:
  "X: Occ_range(Tag, Arity) ==> DenseTree(X)"
apply (erule Occ_rangeE)
apply assumption
done

lemma Occ_range_functionalD:
  "X: Occ_range(Tag, Arity) ==> functional(X)"
apply (erule Occ_rangeE)
apply assumption
done

lemma Occ_range_CorrectArityD:
  "[| X: Occ_range(Tag, Arity); T: Tag |]
        ==> CorrectArity(X, T, Arity(T))"
apply (erule Occ_rangeE)
apply (erule bspec)
apply assumption
done


(** Occ_cons_cond **)
lemma Occ_cons_condD1:
  "[| Occ_cons_cond(Terms, Occ, Tag, Arity); T: Tag |] ==> Arity(T): nat"
apply (unfold Occ_cons_cond_def)
apply blast
done

lemma Occ_cons_condD2:
  "[| Occ_cons_cond(Terms, Occ, Tag, Arity);
      T: Tag; l: list(Pow(list(nat) * Tag));
      Arity(T) = length(l);
      ALL z: length(l). EX N: Terms. nth(z, l) = Occ(N)
   |] ==> EX M: Terms. Occ(M) = Occ_cons(T, l)"
apply (unfold Occ_cons_cond_def)
apply blast
done

lemma Occ_cons_condI:
  "[| !!T. T: Tag ==> Arity(T): nat;
      !!T l. [| T: Tag; l: list(Pow(list(nat) * Tag));
         length(l) = Arity(T);
         ALL z: length(l). EX N: Terms. nth(z, l) = Occ(N) |]
         ==> EX M: Terms. Occ(M) = Occ_cons(T, l)
   |] ==> Occ_cons_cond(Terms, Occ, Tag, Arity)"
apply (unfold Occ_cons_cond_def)
apply (rule conjI)
apply blast
apply (intro ballI impI)
apply simp
done


(** Occ_ind_cond **)
lemma Occ_ind_condD:
  assumes major: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and prem: "M: Terms"
  and indstep:
    "!! l T. [| T: Tag; l: list(Terms);
               Term_cons(T, l): Terms;
               Arity(T) = length(l);
               Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l));
               ALL z: length(l). P(nth(z, l)) |]  ==> P(Term_cons(T, l))"
  shows "P(M)"
apply (rule_tac A="Terms" in CollectD2)
apply (rule major [unfolded Occ_ind_cond_def, THEN spec, THEN mp, THEN bspec])
apply (rule_tac [2] prem)
apply (intro allI impI ballI)
apply (elim conjE)
apply (rule CollectI)
apply assumption
apply (erule indstep)
apply assumption+
apply (rule ballI)
apply (drule bspec, assumption)
apply (erule CollectE)
apply assumption
done

lemma Occ_ind_condI:
  assumes ind:
    "!!P M. [| M: Terms;
             ALL T: Tag. ALL l: list(Terms).
              Term_cons(T, l): Terms &
              Arity(T) = length(l) &
              Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l)) &
              (ALL z: length(l). P(nth(z, l))) --> P(Term_cons(T, l))
            |] ==> P(M)"
   shows "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
apply (unfold Occ_ind_cond_def)
apply (intro allI impI ballI)
apply (erule ind)
apply assumption
done

lemma Occ_ind_cond_Occ_domain:
  assumes major: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and prem: "M: Terms"
  shows "Occ(M) <= list(nat) * Tag"
apply (rule Occ_ind_condD [OF major prem])
apply (erule_tac P="%x. x <= list(nat) * Tag" in ssubst)
apply (rule Occ_cons_type2)
apply assumption
apply simp_all
done

lemma Occ_ind_cond_Occ_induct:
  assumes major: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and prem: "M: Terms"
  and indstep:
     "!! l T. [| T: Tag; l: list(Pow(list(nat) * Tag));
            Occ_cons(T, l) <= list(nat) * Tag;
            length(l) = Arity(T);
            ALL z: length(l). P(nth(z, l)) |]  ==> P(Occ_cons(T, l))"
  shows "P(Occ(M))"
apply (rule Occ_ind_condD [OF major prem])
apply simp
apply (rule indstep)
apply assumption
apply (erule_tac [2] P="%x. x <= list(nat) * Tag" in subst)
apply (erule_tac [2] major [THEN Occ_ind_cond_Occ_domain])
apply (rule map_type)
apply (erule_tac [2] major [THEN Occ_ind_cond_Occ_domain, THEN PowI])
apply assumption
apply (simp_all add: nth_map)
done

lemma Occ_ind_cond_Occ_inj_lemma:
  assumes major: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and prem: "M: Terms"
  shows "ALL N: Terms. Occ(M) = Occ(N) --> M = N"
apply (rule Occ_ind_condD [OF major prem])
apply (rule ballI)
apply (erule_tac M="N" in major [THEN Occ_ind_condD])
apply simp
apply (rule impI)
apply (rule Occ_cons_iff [THEN iffD1, elim_format])
prefer 3 apply assumption

apply (rule map_type)
apply assumption
apply (erule major [THEN Occ_ind_cond_Occ_domain, THEN PowI])

apply (rule map_type)
apply assumption
apply (erule major [THEN Occ_ind_cond_Occ_domain, THEN PowI])
apply (erule conjE)
apply hypsubst
apply simp
apply (rename_tac v T')
apply (rule_tac a="v" and b="l" in ssubst)
apply (rule_tac [2] refl)
apply (rule_tac nth_inj)
defer 1
defer 1
apply assumption+
apply (simp_all add: nth_map)
apply (rule ballI)
apply (erule bspec [THEN bspec, THEN mp])
apply (frule length_type [THEN [2] nat_ltI])
apply simp_all
done

lemma Occ_ind_cond_Occ_inj:
  assumes major: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  shows "[| M: Terms; N: Terms |] ==> Occ(M) = Occ(N) <-> M = N"
apply (rule iffI)
apply (rule major [THEN Occ_ind_cond_Occ_inj_lemma, THEN bspec, THEN mp])
apply assumption+
apply hypsubst
apply (rule refl)
done


(** Monotonisity **)
lemma Occ_shift_mono:
  "X <= Y ==> Occ_shift(b, X) <= Occ_shift(b, Y)"
apply (blast elim!: Occ_shiftE intro!: Occ_shiftI)
done

lemma Occ_subtree_mono:
  "X <= Y ==> Occ_subtree(b, X) <= Occ_subtree(b, Y)"
apply (blast elim!: Occ_subtreeE intro!: Occ_subtreeI)
done

lemma Occ_primary_mono:
  "X <= Y ==> Occ_primary(X) <= Occ_primary(Y)"
apply (blast elim!: Occ_primaryE intro!: Occ_primaryI)
done


(** Finiteness **)
lemma Occ_shift_FinI:
  "[| X: Fin(list(A)*B); b: A |] ==>  Occ_shift(b, X): Fin(list(A)*B)"
apply (erule Fin_induct)
apply (simp add: Occ_shift_simps)
apply (erule SigmaE)
apply (simp add: Occ_shift_simps)
done

lemma Occ_subtree_FinI:
  "X: Fin(list(A)*B) ==>  Occ_subtree(b, X): Fin(list(A)*B)"
apply (erule Fin_induct)
apply (simp add: Occ_subtree_simps)
apply (erule SigmaE)
apply (erule list.cases)
apply (simp_all add: Occ_subtree_simps)
apply (rule impI)
apply hypsubst
apply (rule Fin.intros)
apply (rule SigmaI)
apply assumption+
done

lemma Occ_primary_FinI:
  "X: Fin(list(A)*B) ==>  Occ_primary(X): Fin(list(A)*B)"
apply (erule Fin_induct)
apply (erule_tac [2] SigmaE)
apply (simp_all add: Occ_primary_simps)
done

lemma Occ_cons_FinI:
  "[| l: list(Fin(list(nat)*Tag)); T: Tag |] ==>
                  Occ_cons(T, l): Fin(list(nat)*Tag)"
apply (erule list_append_induct)
apply (simp_all add: Occ_cons_Nil Occ_cons_app_last)
apply (blast intro: length_type Occ_shift_FinI Fin_UnI)
done


(** Occ_fbs_op **)
lemma Occ_fbs_op_continuous:
  "X ~= 0 ==> Occ_fbs_op(Tag, Union(X)) = (UN x: X. Occ_fbs_op(Tag, x))"
apply (unfold Occ_fbs_op_def)
apply (subgoal_tac "{domain(x). x: X} ~= 0")
apply (simp add: continuous_simps list_op_continuous)
apply (erule not_emptyE)
apply (rule not_emptyI)
apply (rule RepFunI)
apply assumption
done

lemma Occ_fbs_mono_inj_pair: 
  assumes major: "X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  and prem: "X ~= 0"
  shows "mono_inj_pair(list_dom(nat), %x. x * Tag , domain)"
apply (rule prem [THEN not_emptyE])
apply (drule major [unfolded Occ_fbs_dom_def, THEN fin_bnd_set_domain [THEN subsetD], THEN PowD, THEN subsetD])
apply (erule SigmaE)
apply (erule Prod_domain_mono_inj_pair)
done

lemma Occ_fbs_mono_inj_pair2:
  assumes prem1: "X <= A * Tag"
  and prem2: "X ~= 0"
  shows "mono_inj_pair(list_dom(nat), %x. x * Tag , domain)"
apply (rule prem2 [THEN not_emptyE])
apply (drule prem1 [THEN subsetD])
apply (erule SigmaE)
apply (erule Prod_domain_mono_inj_pair)
done

lemma Occ_fbs_op_bnd_cont:
  "bnd_cont(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
apply (rule bnd_contI)
apply (erule Occ_fbs_op_continuous)
apply (unfold Occ_fbs_op_def Occ_fbs_dom_def)
apply (case_tac "Tag = 0")
apply simp
apply (erule not_emptyE)
apply (simp add: domain_of_prod)
apply (insert list_op_bnd_mono [THEN bnd_monoD1])
apply blast
done

lemmas Occ_fbs_op_bnd_mono = Occ_fbs_op_bnd_cont
    [THEN bnd_cont_bnd_mono, rule_format]

lemma Occ_fbs_op_lfp_eq:
  "lfp(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)) = list(nat) * Tag"
apply (case_tac "Tag = 0")
apply (simp add: Occ_fbs_dom_def lfp_def Occ_fbs_op_def)
apply (erule not_emptyE)
apply (drule_tac A1=nat in
  mono_inj_pair_lfp_eq [OF Prod_domain_mono_inj_pair list_op_bnd_mono])
apply (fold Occ_fbs_dom_def Occ_fbs_op_def)
apply (erule list_op_lfp_eq [THEN ssubst])
done

lemma Occ_fbs_op_fin_bnd_set_upper_Fin:
  "Fin(list(nat) * Tag) <= fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
apply (insert Occ_fbs_op_bnd_cont [THEN fin_bnd_set_upper_Fin_lfp])
apply (simp add: Occ_fbs_op_lfp_eq)
done

lemma Occ_fbs_op_lfp_lowerbound:
  "X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))
     ==> X <= list(nat) * Tag"
apply (rule Occ_fbs_op_lfp_eq [THEN subst])
apply (rule Occ_fbs_op_bnd_mono [THEN fin_bnd_set_Pow_lfp_lowerbound,
         THEN subsetD, THEN PowD])
apply assumption
done


(** Preservation Properties of Occ_subtree **)
lemma Occ_subtree_preserves_domain:
  "X <= list(A) * B ==> Occ_subtree(b, X) <= list(A) * B"
apply (blast elim!: Occ_subtreeE ConsE)
done

lemma Occ_subtree_preserves_functionality:
  "functional(X) ==> functional(Occ_subtree(a, X))"
apply (rule functionalI)
apply (drule Occ_subtreeD)+
apply (erule functionalD)
apply assumption+
done

lemma Occ_subtree_preserves_CorrectArity:
  assumes prem: "CorrectArity(X, T, n)"
  shows "CorrectArity(Occ_subtree(a, X), T, n)"
apply (rule CorrectArityI)
apply (erule_tac [2] Occ_subtreeE2)
apply (erule Occ_subtreeE2)
apply (drule_tac [2] prem [THEN CorrectArityD2])
apply (drule prem [THEN CorrectArityD1])
apply assumption
prefer 2 apply assumption
apply (erule_tac [2] notE)
apply (erule exE)
apply (rule exI)
apply (rule Occ_subtreeI)
apply simp
apply (erule exE)
apply (drule Occ_subtreeD)
apply (rule exI)
apply simp
done

lemma Occ_subtree_preserves_DenseTree:
  assumes prem: "DenseTree(X)"
  shows "a: nat ==> DenseTree(Occ_subtree(a, X))"
apply (rule DenseTreeI)
apply (drule Occ_subtreeD)
apply (erule prem [THEN DenseTreeE])
apply (rule initseg_ConsI)
apply assumption+
apply (rule exI)
apply (erule Occ_subtreeI)
done

lemma Occ_subtree_preserves_not_empty:
  assumes major: "<[], T>: X"
  and prem: "CorrectArity(X, T, n)"
  and n_nat: "n: nat"
  shows "ALL z: n. Occ_subtree(z, X) ~= 0"
apply (rule ballI)
apply (frule n_nat [THEN nat_into_Ord, THEN [2] ltI])
apply (drule CorrectArityD1 [OF prem major])
apply (erule exE)
apply (rule not_emptyI)
apply (rule Occ_subtreeI)
apply simp
done

lemma Occ_subtree_Occ_fbs_op_lemma:
  "x <= Occ_fbs_op(Tag, Z) ==> Occ_subtree(b, x) <= domain(Z) * Tag"
apply (unfold Occ_fbs_op_def list_op_def)
apply (clarify elim!: Occ_subtreeE)
apply (drule subsetD)
apply assumption
apply (erule SigmaE)
apply (erule CollectE)
apply safe
apply simp_all
apply (erule domainI)
done

lemma Occ_subtree_in_fin_bnd_set:
  assumes prem1: "X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  and prem2: "X ~= 0"
  shows "Occ_subtree(b, X): fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
apply (rule prem1 [THEN Occ_fbs_op_bnd_mono [THEN fin_bnd_set_boundE]])
apply (rule Occ_fbs_op_bnd_mono [THEN fin_bnd_set_subsetI])
apply (rule Occ_subtree_Occ_fbs_op_lemma)
apply (erule subset_trans)
apply assumption
apply (rule Occ_fbs_op_bnd_mono [THEN fin_bnd_setI2])
apply (erule fin_bnd_setE)
apply (unfold fin_bnd_def Occ_fbs_op_def)
apply (erule mono_inj_pair_fin_bnd_lemma 
        [OF Occ_fbs_mono_inj_pair [OF prem1 prem2] list_op_bnd_mono,
          unfolded fin_bnd_def])
done

lemma Occ_subtree_in_Occ_range:
  assumes major: "<Cons(a, l), T>: X"
  and prem: "X: Occ_range(Tag, Arity)"
  and a_nat: "a: nat"
  shows "Occ_subtree(a, X): Occ_range(Tag, Arity)"
apply (rule prem [THEN Occ_rangeE])
apply (rule Occ_rangeI)
apply (rule_tac [5] ballI)
apply (rule_tac [2] not_emptyI)
apply (rule_tac [2] major [THEN Occ_subtreeI])
apply (drule_tac [4] bspec)
apply (assumption | rule a_nat Occ_subtree_in_fin_bnd_set
        Occ_subtree_preserves_functionality
        Occ_subtree_preserves_DenseTree
        Occ_subtree_preserves_CorrectArity)+
done


(** Range of Occurence  **)
lemma Occ_domain_lemma:
  assumes major: "X <= Occ_fbs_dom(Tag)"
  and hinj: "mono_inj_pair(list_dom(nat), %x. x * Tag , domain)"
  and hmono: "bnd_mono(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  shows
    "[|
       Z: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)); 
       X <= Occ_fbs_op(Tag, Z)
     |] ==> X <= list(nat)*Tag"
apply (rule list_op_lfp_eq [THEN ssubst])
apply (rule subst [OF mono_inj_pair_lfp_eq
                   [OF hinj list_op_bnd_mono],
                    unfolded Occ_fbs_dom_def])
apply (fold Occ_fbs_dom_def Occ_fbs_op_def)
apply (rule hmono [THEN fin_bnd_set_Pow_lfp_lowerbound,
                   THEN subsetD, THEN PowD])
apply (erule fin_bnd_setE)
apply (rule major [THEN fin_bnd_setI])
apply (rule hmono [THEN fin_bnd_succ])
apply assumption+
done

lemma Occ_DenseTree_not_empty_lemma:
  assumes major: "X ~= 0"
  and domX: "X <= list(nat) * Tag"
  and hierX: "DenseTree(X)"
  shows "EX N: Tag. <[], N>: X"
apply (rule major [THEN not_emptyE])
apply (frule domX [THEN subsetD])
apply (erule SigmaE)
apply hypsubst
apply (erule hierX [THEN DenseTreeE])
apply (erule initseg_NilI)
apply (frule domX [THEN subsetD])
apply (erule SigmaE2)
apply (erule bexI)
apply assumption
done

lemma Occ_primary_functional_lemma:
  assumes major: "<[], T>: X"
  and funcX: "functional(X)"
  shows "Occ_primary(X) = {<[], T>}"
apply (rule equalityI)
apply (rule subsetI)
apply (erule Occ_primaryE)
apply (drule major [THEN funcX [THEN functionalD]])
apply hypsubst
apply (rule singletonI)
apply (rule subsetI)
apply (erule singletonE)
apply hypsubst
apply (rule major [THEN Occ_primaryI])
done

lemma Occ_range_lemma1:
  assumes Arity_nat: "Arity(T): nat"
  and not_empty: "ALL z: Arity(T). Occ_subtree(z, X) ~= 0"
  and prem1: "ALL y. y <= domain(Z)*Tag -->
               y ~=0 & functional(y) & DenseTree(y) &
                (ALL T: Tag. CorrectArity(y, T, Arity(T))) -->
                       (EX M: Terms. y = Occ(M))"
  and prem2: "X <= Occ_fbs_op(Tag, Z)"
  and funcX: "functional(X)"
  and hierX: "DenseTree(X)"
  and corrX: "ALL T:Tag. CorrectArity(X, T, Arity(T))"
  shows "ALL z: Arity(T). EX N: Terms. Occ_subtree(z, X) = Occ(N)"
apply (rule ballI)
apply (rule prem1 [THEN spec, THEN mp,
        OF prem2 [THEN Occ_subtree_Occ_fbs_op_lemma], THEN mp])
apply (frule Arity_nat [THEN [2] mem_nat_in_nat])
apply (assumption | rule conjI ballI funcX hierX
       corrX [THEN bspec] not_empty [THEN bspec]
       Occ_subtree_preserves_functionality
       Occ_subtree_preserves_DenseTree
       Occ_subtree_preserves_CorrectArity)+
done

lemma Occ_range_lemma2:
  assumes Arity_nat: "Arity(T): nat"
  and domX: "X <= list(nat)*Tag"
  and prem: 
     "ALL z: Arity(T). EX N: Terms. Occ_subtree(z, X) = Occ(N)"
  shows "EX l: list(Pow(list(nat)*Tag)). Arity(T) = length(l) &
            (ALL z: length(l). nth(z, l) = Occ_subtree(z, X)) &
            (ALL z: length(l). EX N: Terms. nth(z, l) = Occ(N))"
apply (rule nth_existence_lemma [elim_format])
apply (rule_tac [2] Arity_nat)
apply (rule ballI)
apply (rule_tac b1="z" in domX [THEN Occ_subtree_preserves_domain, THEN PowI])
apply (erule bexE)
apply (erule conjE)
apply (rule bexI)
prefer 2 apply assumption
apply (rule conjI)
apply (erule sym)
apply (rule conjI)
apply (erule ssubst)
apply assumption
apply (rule ballI)
apply simp
apply (frule prem [THEN bspec])
apply (erule bexE)
apply (rule bexI)
apply assumption+
done

lemma Occ_cons_lemma:
  assumes major: "<[], T>: X"
  and crrX: "CorrectArity(X, T, length(l))"
  and funcX: "functional(X)"
  and hierX: "DenseTree(X)"
  and domX: "X <= list(nat) * Tag"
  and l_list: "l: list(A)"
  and prem: "ALL z: length(l). nth(z, l) = Occ_subtree(z, X)"
  shows "Occ_cons(T, l) = X"
apply (rule sym)
apply (rule domX [THEN Occ_primary_subtree_shift_eq, THEN trans])
apply (simp add: Occ_primary_functional_lemma [OF major funcX])
apply (rule equalityI)
apply (rule subsetI)
apply (erule UnE)
apply (erule singletonE)
apply hypsubst
apply (rule Occ_consI1)
apply (erule UN_E)
apply (erule Occ_shiftE)
apply hypsubst
apply (rule crrX [THEN CorrectArityE])
apply (rule_tac [3] major)
prefer 3 apply assumption
apply (rule_tac [3] l_list [THEN length_type])
apply (rule Occ_consI2)
apply (erule ltD)
apply (drule ltD)
apply (drule prem [THEN bspec])
apply (erule ssubst)
apply assumption
apply (drule Occ_subtreeD)
apply (rule hierX [THEN DenseTreeE])
apply assumption
apply (erule initseg_ConsI)
apply (rule initseg_NilI)
apply (drule domX [THEN subsetD])
apply (erule SigmaE2)
apply (erule ConsE)
apply assumption
apply (rule exI)
apply simp
apply (rule subsetI)
apply (erule Occ_consE)
apply blast
apply hypsubst
apply (rule UnI2)
apply (rule UN_I)
apply (rule_tac [2] Occ_shiftI)
apply (erule l_list [THEN length_type, THEN [2] mem_nat_in_nat])
apply (drule prem [THEN bspec])
apply (erule subst)
apply assumption
done

lemma Occ_fbs_op_fin_bnd_induct:
  assumes major: "X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  and prem: "X ~= 0"
  and indstep:
      "!!X. [| X <= list(nat)*Tag; X ~= 0;
              EX Z: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)).
                X <= Occ_fbs_op(Tag, Z) &
            (ALL Y. Y <= domain(Z)*Tag --> Y ~= 0 -->P(Y)) |] ==> P(X)"
  shows "P(X)"
apply (rule prem [THEN rev_mp])
apply (rule_tac a="X" in mono_inj_pair_fin_bnd_set_induct)
apply (rule Occ_fbs_mono_inj_pair [OF major prem])
apply (rule trivial_mono_inj_pair)
apply (rule Prod_domain_0_eq)
apply (rule list_op_bnd_mono)
apply (fold Occ_fbs_dom_def Occ_fbs_op_def)
apply (rule major)
apply blast
apply (rule impI)
apply (elim bexE conjE)
apply (drule Occ_domain_lemma)
apply (assumption 
       | rule Occ_fbs_mono_inj_pair [OF major prem]
              Occ_fbs_op_bnd_mono)+
apply (rule indstep)
apply (assumption | rule bexI conjI)+
done

lemma Occ_range_existence_lemma:
  assumes major: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and prem: "X: Occ_range(Tag, Arity)"
  shows "EX M: Terms. X = Occ(M)"
apply (rule prem [unfolded Occ_range_def, THEN CollectD2, THEN rev_mp])
apply (rule_tac a="X" in mono_inj_pair_fin_bnd_set_induct)
apply (rule Occ_fbs_mono_inj_pair)
apply (rule prem [unfolded Occ_range_def, THEN CollectD1])
apply (rule prem [unfolded Occ_range_def, THEN CollectD2,
                  THEN conjunct1])
apply (rule trivial_mono_inj_pair)
apply (rule Prod_domain_0_eq)
apply (rule list_op_bnd_mono)
apply (fold Occ_fbs_dom_def Occ_fbs_op_def)
apply (rule prem [unfolded Occ_range_def, THEN CollectD1])
apply blast
apply (rule impI)
apply (elim bexE conjE)
apply (drule Occ_domain_lemma)
apply (rule_tac [2] Occ_fbs_op_bnd_mono)
apply (rule Occ_fbs_mono_inj_pair)
apply (rule prem [unfolded Occ_range_def, THEN CollectD1])
apply (assumption 
       | rule prem [unfolded Occ_range_def, THEN CollectD2,
                    THEN conjunct1])+
apply (frule Occ_DenseTree_not_empty_lemma)
apply assumption+
apply (erule bexE)
apply (frule bspec)
apply assumption
apply (frule major [THEN Occ_cons_condD1])
apply (frule Occ_subtree_preserves_not_empty)
apply assumption+
apply (frule_tac Arity=Arity in Occ_range_lemma1)
apply assumption+
apply (frule_tac Arity=Arity in Occ_range_lemma2)
apply assumption+
apply (elim bexE conjE)
apply (frule major [THEN Occ_cons_condD2])
apply assumption+
apply (erule bexE)
apply (frule_tac l="l" in Occ_cons_lemma)
apply (erule_tac P="%z. CorrectArity(x, N, z)" in subst)
apply assumption+
apply (rule bexI)
apply (erule sym [THEN trans])
apply (erule sym)
apply assumption
done

lemma Occ_range_depth_induct:
  assumes major: "X: Occ_range(Tag, Arity)"
  and indstep:
     "!!X. [| X <= list(nat) * Tag; X: Occ_range(Tag, Arity);
              EX Z: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag)).
                X <= Occ_fbs_op(Tag, Z) &
            (ALL Y: Occ_range(Tag, Arity). Y <= domain(Z)*Tag --> P(Y))
      |] ==> P(X)"
  shows "P(X)"
apply (rule major [unfolded Occ_range_def, THEN rev_mp])
apply (rule Occ_fbs_op_fin_bnd_induct
       [OF major [unfolded Occ_range_def, THEN CollectD1]
           major [unfolded Occ_range_def, THEN CollectD2, THEN conjunct1]])
apply (rule impI)
apply (rule indstep [unfolded Occ_range_def])
apply assumption+
apply (elim bexE conjE)
apply (rule bexI)
prefer 2 apply assumption
apply (erule conjI)
apply (rule impI [THEN ballI])
apply (erule spec [THEN mp, THEN mp, THEN mp])
apply (erule_tac [2] CollectE conjE)+
apply assumption+
done


(** Occ_in_Occ_range **)
lemma Occ_cons_preserves_functionality:
  "[| ALL z: length(l). functional(nth(z, l)) |]
         ==> functional(Occ_cons(T, l))"
apply (rule functionalI)
apply (erule Occ_consE)
apply (erule Occ_consE)
apply (erule_tac [3] Occ_consE)
apply (drule_tac [4] bspec)
prefer 4 apply assumption
apply simp_all
apply (blast dest: functionalD)
done

lemma Occ_cons_preserves_DenseTree:
  assumes prem: "ALL z: length(l). DenseTree(nth(z, l))"
  and l_list: "l: list(A)"
  shows "DenseTree(Occ_cons(T, l))"
apply (rule DenseTreeI)
apply (erule Occ_consE)
apply (erule Pair_iff [THEN iffD1, THEN conjE])
apply hypsubst
apply (erule initseg_NilE)
apply hypsubst
apply (rule exI)
apply (rule Occ_consI1)
apply (erule Pair_iff [THEN iffD1, THEN conjE])
apply hypsubst
apply (erule initseg_ConsE)
apply hypsubst
apply (rule exI)
apply (rule Occ_consI1)
apply hypsubst
apply (frule prem [THEN bspec])
apply (erule DenseTreeE)
apply (assumption
       | rule Occ_consI2 exI ltI
            l_list [THEN length_type, THEN nat_into_Ord])+
done

lemma Occ_cons_preserves_CorrectArity:
  assumes corr: "ALL z: length(l). CorrectArity(nth(z, l), U, n)"
  and hier: "ALL z: length(l). DenseTree(nth(z, l))"
  and not_empty: "ALL z: length(l). nth(z, l) ~= 0"
  and domnth: "ALL z: length(l). nth(z, l) <= list(nat) * Tag"
  and prem: "T = U ==> n = length(l)"
  shows "CorrectArity(Occ_cons(T, l), U, n)"
apply (rule CorrectArityI)
apply (erule Occ_consE)
apply (erule Pair_iff [THEN iffD1, THEN conjE])
apply (frule sym [THEN prem])
apply hypsubst
apply (frule ltD)
apply (frule not_empty [THEN bspec])
apply (frule domnth [THEN bspec])
apply (frule hier [THEN bspec])
apply (erule not_emptyE)
apply (drule subsetD)
apply assumption
apply (erule SigmaE)
apply hypsubst
apply (erule DenseTreeE)
apply assumption
apply (erule initseg_NilI)
apply (rule exI)
apply simp
apply (erule Occ_consI2)
apply assumption
apply (erule Pair_iff [THEN iffD1, THEN conjE])
apply (frule corr [THEN bspec])
apply (drule CorrectArityD1)
apply hypsubst
apply assumption+
apply (erule exE)
apply (rule exI)
apply simp
apply (erule Occ_consI2)
apply assumption
apply (erule Occ_consE)
apply (elim exE Occ_consE)
apply (erule_tac [3] exE Occ_consE)+
apply simp
prefer 2 apply simp
apply simp
apply clarify
apply (frule sym [THEN prem])
apply hypsubst
apply (erule leE)
apply (drule ltD)
apply (erule mem_asym, assumption)
apply hypsubst
apply (erule mem_irrefl)
apply (frule corr [THEN bspec])
apply simp
apply clarify
apply (drule CorrectArityD2)
apply assumption+
apply (erule notE)
apply (erule exI)
done

lemma Occ_range_domain_lemma:
  "X: Occ_range(Tag, Arity) ==> X <= list(nat) * Tag"
apply (erule Occ_rangeE)
apply (drule Occ_fbs_op_bnd_mono [THEN fin_bnd_set_Pow_lfp_lowerbound, THEN subsetD])
apply (drule PowD)
apply (rule Occ_fbs_op_lfp_eq [THEN subst])
apply assumption
done

lemma Occ_cons_in_fin_bnd_set:
  assumes hmono: "bnd_mono(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  and t_tag: "T: Tag"
  and l_list: "l: list(Pow(list(nat)*Tag))"
  and prem: 
    "ALL z: length(l). nth(z, l): fin_bnd_set(Occ_fbs_dom(Tag),
                                                Occ_fbs_op(Tag))"
  shows "Occ_cons(T, l): fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
apply (rule prem [THEN rev_mp])
apply (rule l_list [THEN list_append_induct])
apply (simp_all add: Occ_cons_Nil Occ_cons_app_last)
apply (rule hmono [THEN fin_bnd_set_succI])
prefer 2 apply (rule fin_bnd_set_0I)
apply (simp add: Occ_fbs_op_def list_op_def)
apply (rule conjI)
apply (rule nat_subset_univ [THEN [2] list_into_univ])
apply (rule list.intros)
apply (rule t_tag)
apply (rule impI)
apply (rule hmono [THEN fin_bnd_set_UnI])
apply (erule mp)
apply simp
apply (rule hmono [THEN fin_bnd_set_succI])
apply (simp add: Occ_fbs_op_def list_op_def)
apply (rule subsetI)
apply (erule Occ_shiftE)
apply hypsubst
apply (rule SigmaI)
apply (rule CollectI)
apply (rule nat_subset_univ [THEN [2] list_into_univ])
apply (rule list.intros)
apply (erule length_type)
apply (drule subsetD, assumption)
apply (erule SigmaD1)
apply (rule disjI2)
apply (intro exI)
apply (assumption | rule conjI refl length_type domainI)+
apply (drule subsetD, assumption)
apply (erule SigmaD2)
apply (erule conjE)
apply assumption
done

lemma Occ_ind_cond_Occ_in_Occ_range:
  assumes major: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and prem: "M: Terms"
  shows "Occ(M): Occ_range(Tag, Arity)"
apply (rule prem [THEN major [THEN Occ_ind_cond_Occ_induct]])
apply (rule Occ_rangeI)
apply (rule_tac [2] Occ_consI1 [THEN not_emptyI])
apply (rule_tac [4] ballI)

apply (rule Occ_cons_in_fin_bnd_set)
apply (rule Occ_fbs_op_bnd_mono)
apply assumption+
apply (rule ballI)
apply (drule bspec, assumption)
apply (erule Occ_rangeE)
apply assumption

apply (rule Occ_cons_preserves_functionality)
apply (rule ballI)
apply (drule bspec, assumption)
apply (erule Occ_rangeE)
apply assumption

apply (rule Occ_cons_preserves_DenseTree)
apply (rule ballI)
apply (drule bspec, assumption)
apply (erule Occ_rangeE)
apply assumption+

apply (rule Occ_cons_preserves_CorrectArity)
apply (rule ballI)
apply (drule bspec, assumption)
apply (erule Occ_rangeE)
apply (erule bspec)
apply assumption

apply (rule ballI)
apply (drule bspec, assumption)
apply (erule Occ_rangeE)
apply assumption

apply (rule ballI)
apply (drule bspec, assumption)
apply (erule Occ_rangeE)
apply assumption

apply (rule ballI)
apply (drule bspec, assumption)
apply (erule Occ_range_domain_lemma)
apply hypsubst
apply (erule sym)
done

lemma Occ_ind_cond_Occ_FinI:
  assumes hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and prem: "M: Terms"
  shows "Occ(M): Fin(list(nat) * Tag)"
apply (rule Occ_ind_cond_Occ_induct [OF hind prem])
apply (rule Occ_cons_FinI)
apply (erule nth_convert_list_type)
apply assumption+
done
  
lemma Occ_ind_cond_Occ_not_empty_lemma:
  assumes hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and major: "M: Terms"
  shows "EX T: Tag. <[], T>: Occ(M)"
apply (rule Occ_ind_cond_Occ_in_Occ_range [OF hind major, THEN Occ_rangeE])
apply (rule Occ_DenseTree_not_empty_lemma)
apply (assumption | rule Occ_ind_cond_Occ_domain [OF hind major])+
done

lemma Occ_range_convert_lemma:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and major: "X: Occ_range(Tag, Arity)"
  and prem: "!!M. M: Terms ==> P(Occ(M))"
  shows "P(X)"
apply (rule Occ_range_existence_lemma [OF hcons major, THEN bexE])
apply (erule ssubst)
apply (erule prem)
done

lemma Occ_range_unique_existence_lemma:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and major: "X: Occ_range(Tag, Arity)"
  shows "EX! M. M: Terms & X = Occ(M)"
apply (rule Occ_range_existence_lemma [OF hcons major, THEN bexE])
apply (rule ex1I)
apply (rule_tac [2] hind [THEN Occ_ind_cond_Occ_inj, THEN iffD1])
apply safe
apply (assumption | rule refl sym)+
done

lemma def_Occinv_type:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and major: "X: Occ_range(Tag, Arity)"
  shows "Occinv(X): Terms"
apply (unfold hinv)
apply (rule conjunct1)
apply (rule Occ_range_unique_existence_lemma
        [OF hcons hind major, THEN theI])
done

lemma def_Occ_Occinv:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and major: "X: Occ_range(Tag, Arity)"
  shows "Occ(Occinv(X)) = X"
apply (unfold hinv)
apply (rule conjunct2 [THEN sym])
apply (rule Occ_range_unique_existence_lemma
        [OF hcons hind major, THEN theI])
done

lemma def_Occinv_Occ:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and major: "M: Terms"
  shows "Occinv(Occ(M)) = M"
apply (unfold hinv)
apply (rule the_equality)
apply (rule_tac [2] hind [THEN Occ_ind_cond_Occ_inj, THEN iffD1])
apply (assumption | erule conjE | rule major refl conjI sym)+
done

lemma def_Occinv_lemma:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and major: "X: Occ_range(Tag, Arity)"
  shows
   "ALL T: Tag. ALL l: list(Terms).
      <[], T>: X &
      Arity(T) = length(l) &
      (ALL z: length(l). nth(z, l) = Occinv(Occ_subtree(z, X)))
    --> Occinv(X) = Term_cons(T, l)"
apply (rule Occ_range_convert_lemma [OF hcons major])
apply (erule hind [THEN Occ_ind_condD])
apply (intro ballI impI)
apply (elim conjE)
apply (rename_tac U m)
apply (subgoal_tac "U = T" "m = l")
apply hypsubst
apply (erule def_Occinv_Occ [OF hcons hind hinv])
prefer 2
apply (frule hind [THEN Occ_ind_cond_Occ_in_Occ_range])
apply (erule Occ_rangeE)
apply (erule functionalD)
apply assumption
apply simp
apply (rule Occ_consI1)
apply (rule nth_inj)
prefer 2
apply simp
prefer 2 apply assumption
prefer 2 apply assumption
apply hypsubst
apply (rule ballI)
apply simp
apply (rule_tac P="%x. Occinv(x) = nth(z, l)" in
         Occ_subtree_Occ_cons [THEN ssubst])
apply (erule mem_nat_in_nat)
apply (erule length_type)
apply (erule map_type)
apply (erule hind [THEN Occ_ind_cond_Occ_domain, THEN PowI])
apply (rule_tac P="%x. Occinv(x) = nth(z, l)" in nth_map [THEN ssubst])
apply assumption
apply (erule ltI)
apply (erule length_type [THEN nat_into_Ord])
apply (rule def_Occinv_Occ [OF hcons hind hinv])
apply (rule nth_type2, assumption)
apply (erule ltI)
apply (erule length_type [THEN nat_into_Ord])
done

lemma def_Occinv:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and major: "<[], T>: X"
  and prem: "X: Occ_range(Tag, Arity)"
  shows
    "[|
        T: Tag; l: list(Terms); Arity(T) = length(l);
        ALL z: length(l). nth(z, l) = Occinv(Occ_subtree(z, X))
     |] ==>  Occinv(X) = Term_cons(T, l)"
apply (rule def_Occinv_lemma [OF hcons hind hinv prem,
         THEN bspec, THEN bspec, THEN mp])
apply (assumption | rule conjI major)+
done

lemma def_Occinv2:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and major: "Occ_cons(T, l): Occ_range(Tag, Arity)"
  shows
    "[| T: Tag; l: list(Pow(list(nat)*Tag)); Arity(T) = length(l)
     |] ==>  Occinv(Occ_cons(T, l)) = Term_cons(T, map(Occinv, l))"
apply (rule def_Occinv [OF hcons hind hinv Occ_consI1 major, THEN trans])
apply (rule_tac [5] refl)
apply (rule_tac [2] nth_convert_list_type)
apply (rule_tac [2] map_type2)
apply (simp_all add: nth_map)
apply (rule ballI)
apply (rule_tac [2] ballI)
prefer 2 apply (simp add: Occ_subtree_Occ_cons)
apply (rule def_Occinv_type [OF hcons hind hinv])
apply (subgoal_tac "z: nat")
prefer 2 apply (erule mem_nat_in_nat)
apply (erule length_type)
apply (rule Occ_subtree_Occ_cons [THEN subst])
apply assumption+
apply (rule major [THEN Occ_rangeE])
apply (drule bspec, assumption)
apply (erule CorrectArityD1 [THEN exE])
apply (rule Occ_consI1)
apply simp
apply (erule nat_into_Ord [THEN [2] ltI])
apply (erule length_type)
apply simp
apply (erule Occ_cons_ConsE)
apply (rule Occ_subtree_in_Occ_range)
apply (erule Occ_consI2)
apply (assumption | rule major)+
done

lemma def_Occinv_convert_lemma:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and major: "M: Terms"
  and prem: "!!X. X: Occ_range(Tag, Arity) ==> P(Occinv(X))"
  shows "P(M)"
apply (insert major [THEN hind [THEN Occ_ind_cond_Occ_in_Occ_range, THEN prem]])
apply (simp add: def_Occinv_Occ [OF hcons hind hinv major])
done

lemma def_Terms_depth_induct:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and major: "M: Terms"
  and indstep:
       "!!M Z. [| Occ(M) <= list(nat) * Tag; M: Terms;
            Z: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag));
            Occ(M) <= Occ_fbs_op(Tag, Z);
            ALL N: Terms. Occ(N) <= domain(Z)*Tag --> P(N)
        |] ==> P(M)"
  shows "P(M)"
apply (rule def_Occinv_convert_lemma [OF hcons hind hinv major])
apply (erule Occ_range_depth_induct)
apply safe
apply (rule indstep)
apply (erule_tac [2] def_Occinv_type [OF hcons hind hinv])
apply (simp_all add: def_Occ_Occinv [OF hcons hind hinv])
apply (intro ballI impI)
apply (drule bspec [THEN mp])
apply (erule hind [THEN Occ_ind_cond_Occ_in_Occ_range])
apply assumption
apply (simp add: def_Occinv_Occ [OF hcons hind hinv])
done

end
