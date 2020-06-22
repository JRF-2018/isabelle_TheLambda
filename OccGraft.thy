(*
    File:        OccGraft.thy
    Time-stamp:  <2015-12-25T10:47:28Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory OccGraft imports SubOcc begin

definition lists_subtree :: "[i, i] => i" where
"lists_subtree(b, W) == {z. y: W, y = Cons(b, z)}"

definition Occ_Shift :: "[i, i] => i" where
"Occ_Shift(m, X) == {z. y: X, EX l T. z = <m@l, T> & y = <l, T>}"

definition Incomparable :: "i=>o" where
"Incomparable(W) == ALL l: W. ALL m: W.
           initseg(nat, l, m) | initseg(nat, m, l) --> l = m"

definition Occ_Graft1 :: "[i, i, i] => i" where
"Occ_Graft1(X, l, Y) == (X - {u: X. EX m T. u = <m, T> &
                                       initseg(nat, l, m)}) Un
                         Occ_Shift(l, Y)"

definition Occ_Graft :: "[i, i, i] => i" where
"Occ_Graft(X, W, Y)  == (X - (UN l: W. {u: X. EX m T. u = <m, T> &
                                                initseg(nat, l, m)}))
                       Un (UN l: W. Occ_Shift(l, Y))"


(** lists_subtree **)
lemma lists_subtreeI:
  "Cons(b, l): X ==> l: lists_subtree(b, X)"
apply (unfold lists_subtree_def)
apply (rule ReplaceI)
prefer 2 apply assumption
apply (rule refl)
apply simp
done

lemma lists_subtreeD:
  "l: lists_subtree(b, X) ==> Cons(b, l): X"
apply (unfold lists_subtree_def)
apply blast
done

lemma lists_subtreeE:
  "[| l: lists_subtree(b, X);
      Cons(b, l): X ==> R |] ==> R"
apply (unfold lists_subtree_def)
apply blast
done

lemma lists_subtree_domain_eq:
  "lists_subtree(b, domain(X)) = domain(Occ_subtree(b, X))"
apply (rule equalityI)
apply (blast intro: Occ_subtreeI lists_subtreeI
         elim!: Occ_subtreeE lists_subtreeE)+
done

lemma lists_subtree_mono:
  "X <= W ==> lists_subtree(b, X) <= lists_subtree(b, W)"
apply (blast intro: lists_subtreeI elim!: lists_subtreeE)
done


(** Occ_Shift **)
lemma Occ_ShiftI:
  "<l, T>: X ==> <m@l, T>: Occ_Shift(m, X)"
apply (unfold Occ_Shift_def)
apply blast
done

lemma Occ_ShiftD:
  "[| <m@l, T>: Occ_Shift(m, X); m: list(A) |] ==> <l, T>: X"
apply (unfold Occ_Shift_def)
apply (elim ReplaceE exE conjE)
apply simp
done

lemma Occ_ShiftE:
  "[| x: Occ_Shift(m, X);
      !!l T. [| x = <m@l, T>; <l, T>: X |] ==> R
   |]==> R"
apply (unfold Occ_Shift_def)
apply blast
done

lemma Occ_ShiftE2:
  "[| <n, T>: Occ_Shift(m, X);
      !!l. [| n = m@l; <l, T>: X |] ==> R
   |]==> R"
apply (unfold Occ_Shift_def)
apply blast
done

lemma Occ_Shift_0:
  "Occ_Shift(m, 0) = 0"
apply (unfold Occ_Shift_def)
apply blast
done

lemma Occ_Shift_Nil:
  "X <= A * B ==> Occ_Shift([], X) = X"
apply (unfold Occ_Shift_def)
apply simp
apply blast
done

lemma Occ_Shift_Cons:
  "Occ_Shift(Cons(a, l), X) = Occ_shift(a, Occ_Shift(l, X))"
apply (rule equalityI)
apply (safe elim!: Occ_shiftE Occ_ShiftE)
apply simp
apply (blast intro: Occ_shiftI Occ_ShiftI)
apply (simp del: app_Cons add: app_Cons [THEN sym])
apply (rule Occ_ShiftI)
apply assumption
done

lemma Occ_Shift_domain:
  "[| X <= list(A) * B; m: list(A) |] ==> Occ_Shift(m, X) <= list(A) * B"
apply (blast intro: app_type elim!: Occ_ShiftE)
done

lemma Occ_Shift_app:
  assumes prem1: "l: list(A)"
  and prem2: "m: list(B)"
  and prem3: "X <= list(B) * D"
  shows "Occ_Shift(l@m, X) = Occ_Shift(l, Occ_Shift(m, X))"
apply (rule prem3 [THEN rev_mp])
apply (rule_tac x="X" in spec)
apply (rule prem1 [THEN list.induct])
apply (intro impI allI)
apply (drule Occ_Shift_domain)
apply (rule prem2)
apply (simp_all add: Occ_Shift_Nil Occ_Shift_Cons)
done


(** Incomparable **)
lemma IncomparableI:
  "[| !!l m. [| l: W; m: W; initseg(nat, l, m) |] ==> l = m |]
     ==> Incomparable(W)"
apply (unfold Incomparable_def)
apply blast
done

lemma IncomparableD:
  "[| Incomparable(W);
      initseg(nat, l, m);
      l: W; m: W |] ==> l = m"
apply (unfold Incomparable_def)
apply blast
done

lemma Incomparable_lists_subtree:
  assumes major: "Incomparable(W)"
  and prem: "a: nat"
  shows "Incomparable(lists_subtree(a, W))"
apply (rule IncomparableI)
apply (elim lists_subtreeE)
apply (drule prem [THEN initseg_ConsI])
apply (drule major [THEN IncomparableD])
apply assumption+
apply simp
done

lemma Incomparable_subset:
  assumes major: "Incomparable(W)"
  and prem: "X <= W"
  shows "Incomparable(X)"
apply (rule IncomparableI)
apply (erule major [THEN IncomparableD])
apply (erule prem [THEN subsetD])+
done

lemma Incomparable_CorrectArity_0_lemma:
  assumes major: "initseg(nat, l, m)"
  and prem1: "<l, T>: X"
  and prem2: "<m, U>: X"
  and hierX: "DenseTree(X)"
  and corrT: "CorrectArity(X, T, 0)"
  and m_list: "m: list(nat)"
  shows "l = m"
apply (rule prem2 [THEN rev_mp])
apply (rule prem1 [THEN rev_mp])
apply (rule major [THEN rev_mp])
apply (rule_tac x="U" in spec)
apply (rule m_list [THEN list_append_induct])
apply (intro allI impI)
apply (erule initseg_NilE)
apply assumption
apply (intro allI impI)
apply (erule  initseg_right_appE)
apply assumption
apply (rule corrT [THEN CorrectArityD2, THEN notE])
apply assumption
apply (erule nat_into_Ord [THEN Ord_0_le])
apply (rule hierX [THEN DenseTreeE])
apply (rule_tac [2] initseg_appI1)
apply assumption+
apply (drule spec)
apply (drule mp, assumption)+
apply hypsubst
apply (erule exI)
apply (rename_tac m n)
apply (erule_tac a="m" in list.cases)
apply hypsubst
apply simp
apply (rule corrT [THEN CorrectArityD2, THEN notE])
apply (rule_tac [3] exI)
apply (erule_tac [2] nat_into_Ord [THEN Ord_0_le])
apply assumption
apply hypsubst
apply assumption
apply simp
done

lemma Incomparable_CorrectArity_0:
  assumes domX: "X <= list(nat)* B"
  and hierX: "DenseTree(X)"
  shows "Incomparable(domain({<l, T>: X. CorrectArity(X, T, 0)}))"
apply (rule IncomparableI)
apply (elim domainE CollectE)
apply simp
apply (erule Incomparable_CorrectArity_0_lemma)
apply (erule_tac [5] domX [THEN subsetD, THEN SigmaD1])
apply (assumption | rule hierX)+
done


(** Occ_Graft1 **)
lemma Occ_Graft1I1:
  "[| <l, T>: X; ~initseg(nat, m, l) |]
      ==> <l, T>: Occ_Graft1(X, m, Y)"
apply (unfold Occ_Graft1_def)
apply blast
done

lemma Occ_Graft1I2:
  "<l, T>: Occ_Shift(m, Y) ==> <l, T>: Occ_Graft1(X, m, Y)"
apply (unfold Occ_Graft1_def)
apply blast
done

lemma Occ_Graft1E:
  "[| x: Occ_Graft1(X, m, Y);
      X <= A * B;
      !! l T. [| x = <l, T>; <l, T>: X; l: A; T: B;
                ~initseg(nat, m, l) |] ==> R;
      x: Occ_Shift(m, Y) ==> R
   |] ==> R"
apply (unfold Occ_Graft1_def)
apply blast
done

lemma Occ_Graft1_domain:
  assumes domX: "X <= list(A) * B"
  and domY: "Y <= list(A) * B"
  and m_list: "m: list(A)"
  shows "Occ_Graft1(X, m, Y) <= list(A) * B"
apply (rule subsetI)
apply (erule Occ_Graft1E)
apply (rule domX)
apply (erule_tac [2] Occ_Shift_domain [OF domY m_list, THEN subsetD])
apply blast
done

lemma Occ_Graft1_Nil:
  assumes prem1: "X <= list(nat) * B"
  and prem2: "Y <= list(nat) * D"
  shows "Occ_Graft1(X, [], Y) = Y"
apply (rule equalityI)
apply (safe elim!: prem1 [THEN [2] Occ_Graft1E] Occ_ShiftE)
prefer 2 apply simp
apply (erule notE)
apply (erule initseg_NilI)
apply (frule prem2 [THEN subsetD])
apply (erule SigmaE)
apply hypsubst
apply (rule Occ_Graft1I2)
apply (rule_tac P="%x. <x, y>: Occ_Shift([], Y)"
        in app_Nil [THEN subst])
apply (erule Occ_ShiftI)
done

lemma Occ_Graft1_Occ_cons_Cons:
  "[| T: Tag; l: list(Pow(list(nat)*Tag)); m: list(nat);
      a: length(l) |] ==>
    Occ_Graft1(Occ_cons(T, l), Cons(a, m), Y) =
        Occ_cons(T, mapnth(%x r. if(a = x, Occ_Graft1(r, m, Y), r), l))"
apply (rule equalityI)
apply (safe elim!: Occ_cons_type [THEN [2] Occ_Graft1E]
           Occ_ShiftE Occ_consE)
apply assumption+
apply (rule Occ_consI1)
prefer 3
apply (rule Occ_Graft1I1)
apply (rule Occ_consI1)
apply (rule notI)
apply (erule initseg_NilE)
apply simp
apply (rule Occ_consI2)
apply (simp add: length_mapnth) 
apply (simp add: nth_mapnth)
apply (rule impI)
apply hypsubst
apply (rule Occ_Graft1I1)
apply assumption
apply (rule notI)
apply (erule notE)
apply (rule initseg_ConsI)
apply (erule mem_nat_in_nat)
apply (erule length_type)
apply assumption
apply simp
apply (rule Occ_consI2)
apply (simp add: length_mapnth)
apply (simp add: nth_mapnth)
apply (rule Occ_Graft1I2)
apply (rule Occ_ShiftI)
apply assumption
apply (simp add: length_mapnth nth_mapnth)
apply (rename_tac b n U)
apply (case_tac "a = b")
apply simp_all
apply (safe elim!: Occ_Graft1E Occ_ShiftE)
apply (frule nth_type2)
apply (erule ltI)
apply (erule length_type [THEN nat_into_Ord])
apply (drule PowD)
apply (drule subsetD)
apply assumption+
apply (rule Occ_Graft1I1)
apply (rule Occ_consI2)
apply assumption+
apply (rule notI)
apply (erule notE)
apply (erule initseg_ConsE)
apply simp
apply simp
apply (rule Occ_Graft1I2)
apply (simp add: Occ_Shift_Cons)
apply (rule Occ_shiftI)
apply (erule Occ_ShiftI)
apply (rule Occ_Graft1I1)
apply (rule Occ_consI2)
apply assumption+
apply (rule notI)
apply (erule initseg_ConsE)
apply simp_all
done


(** Occ_Graft **)
lemma Occ_GraftI1:
  "[| <l, T>: X; ~(EX m: W. initseg(nat, m, l)) |]
      ==> <l, T>: Occ_Graft(X, W, Y)"
apply (unfold Occ_Graft_def)
apply blast
done

lemma Occ_GraftI2:
  "[| m: W; <l, T>: Occ_Shift(m, Y) |]
           ==> <l, T>: Occ_Graft(X, W, Y)"
apply (unfold Occ_Graft_def)
apply blast
done

lemma Occ_GraftE:
  assumes major: "x: Occ_Graft(X, W, Y)"
  and prem: "X <= A * B"
  and prem1:
     "!! l T. [| x = <l, T>; <l, T>: X; l: A; T: B;
                ~(EX m: W. initseg(nat, m, l)) |] ==> R"
  and prem2:
     "!! m. [| m: W; x: Occ_Shift(m, Y) |] ==> R"
  shows "R"
apply (rule major [unfolded Occ_Graft_def, THEN UnE])
apply (erule_tac [2] UN_E)
apply (rule_tac [2] prem2)
apply (erule DiffE)
apply (frule prem [THEN subsetD])
apply (erule SigmaE)
apply (rule prem1)
prefer 2 apply hypsubst
apply (rule_tac [5] notI)
apply (erule_tac [5] notE)
apply (erule_tac [5] bexE)
apply (assumption | rule UN_I CollectI exI conjI)+
done

lemma Occ_Graft_domain:
  assumes domX: "X <= list(A) * B"
  and domY: "Y <= list(A) * B"
  and domW: "W <= domain(X)"
  shows "Occ_Graft(X, W, Y) <= list(A) * B"
apply (rule subsetI)
apply (erule Occ_GraftE)
apply (rule domX)
apply blast
apply (rule domY [THEN Occ_Shift_domain, THEN subsetD])
apply (drule domW [THEN subsetD])
apply (erule domainE)
apply (drule domX [THEN subsetD])
apply (erule SigmaD1)
apply assumption
done

lemma Occ_Graft_0:
  "Occ_Graft(X, 0, Y) = X"
apply (unfold Occ_Graft_def)
apply simp
done

lemma Occ_Graft_cons:
  assumes prem: "Incomparable(cons(a, W))"
  and domW: "cons(a, W) <= domain(X)"
  and domX: "X <= list(nat) * Tag"
  and domY: "Y <= list(nat) * Tag"
  shows "Occ_Graft(X, cons(a, W), Y) =
               Occ_Graft1(Occ_Graft(X, W - {a}, Y), a, Y)"
apply (rule equalityI)
apply (rule_tac [2] subsetI)
apply (rule subsetI)
apply (erule Occ_GraftE)
apply (rule domX)
apply (erule_tac [2] Occ_ShiftE)
apply (erule_tac [3] Occ_Graft1E)
apply (rule_tac [3] Occ_Graft_domain)
apply (rule_tac [5] domW [THEN [2] subset_trans])
prefer 3 apply (rule domX)
prefer 3 apply (rule domY)
prefer 3 apply blast
apply (erule_tac [3] Occ_GraftE)
apply (rule_tac [3] domX)
apply (erule_tac [5] Occ_ShiftE)
apply (erule_tac [4] Occ_ShiftE2)
prefer 5
apply hypsubst
apply (rule Occ_GraftI2)
prefer 2 apply (rule Occ_ShiftI)
apply assumption
apply (rule consI1)
prefer 4
apply hypsubst
apply (rule Occ_GraftI2)
prefer 2 apply (rule Occ_ShiftI)
apply assumption
apply blast
prefer 3
apply hypsubst
apply (rule Occ_GraftI1)
apply simp
apply blast
apply hypsubst
apply (rule Occ_Graft1I1)
apply (rule Occ_GraftI1)
apply assumption
apply blast
apply blast

apply (case_tac "m = a")
apply hypsubst
apply (rule Occ_Graft1I2)
apply (erule Occ_ShiftI)
apply hypsubst
apply (rule Occ_Graft1I1)
apply (rule Occ_GraftI2)
apply (rule_tac [2] Occ_ShiftI)
apply blast

apply assumption
apply (rule notI)
apply (erule initseg_right_appE)
apply (drule domW [THEN subsetD])
apply (erule domainE)
apply (erule domX [THEN subsetD, THEN SigmaD1])
apply (drule_tac [2] prem [THEN IncomparableD])
apply (drule_tac [1] prem [THEN IncomparableD])
defer 3
apply (assumption | rule consI1)+
apply blast+
done

lemma Occ_Graft_cons2:
  assumes prem: "Incomparable(cons(a, W))"
  and domW: "cons(a, W) <= domain(X)"
  and domX: "X <= list(nat) * Tag"
  and domY: "Y <= list(nat) * Tag"
  shows "Occ_Graft(X, cons(a, W), Y) =
               Occ_Graft(Occ_Graft1(X, a, Y), W - {a}, Y)"
apply (rule equalityI)
apply (rule_tac [2] subsetI)
apply (rule subsetI)
apply (erule Occ_GraftE)
apply (rule domX)
apply (erule_tac [2] Occ_ShiftE)
apply (erule_tac [3] Occ_GraftE)
apply (rule_tac [3] Occ_Graft1_domain)
apply (insert consI1 [THEN domW [THEN subsetD]])
apply (erule_tac [5] domainE)
apply (erule_tac [5] domX [THEN subsetD, THEN SigmaD1])
apply (rule_tac [3] domX domY)+
apply (erule_tac [3] Occ_Graft1E)
apply (rule_tac [3] domX)
apply (erule_tac [5] Occ_ShiftE)
apply (erule_tac [4]  Occ_ShiftE2)
apply (simp_all del: cons_iff)
apply (rule_tac [5] Occ_GraftI2)
apply (rule_tac [4] Occ_GraftI2)
apply (rule_tac [7] Occ_ShiftI)
apply (rule_tac [5] Occ_ShiftI)
prefer 7 apply assumption
prefer 6 apply (erule conjE, erule consI2)
prefer 5 apply assumption
prefer 4 apply (rule consI1)
apply (erule conjE)
apply (rule Occ_GraftI1)
apply (rule Occ_Graft1I1)
apply assumption+
apply blast
apply (case_tac "m = a")
apply hypsubst
apply (rule Occ_GraftI1)
apply (rule Occ_Graft1I2)
apply (erule Occ_ShiftI)
apply (rule notI)
apply clarify
apply (erule initseg_right_appE)
apply (rule consI1 [THEN domW [THEN subsetD], THEN domainE])
apply (erule domX [THEN subsetD, THEN SigmaD1])
apply (rule prem [THEN IncomparableD])
apply (assumption | (erule consI2) | (rule consI1))+
apply (rule prem [THEN IncomparableD, THEN sym])
apply (assumption | (erule consI2) | (rule consI1))+
apply (rule Occ_GraftI2)
apply (rule_tac [2] Occ_ShiftI)
apply blast
apply assumption
apply (rule Occ_GraftI1)
apply assumption
apply blast
done

lemma Occ_Graft_Nil:
  "[| X <= list(nat) * Tag; Y <= A * B |] ==>
      Occ_Graft(X, {[]}, Y) = Y"
apply (unfold Occ_Graft_def)
apply (rule equalityI)
apply safe
apply (erule notE)
apply (rule singletonI [THEN UN_I])
apply (blast intro: initseg_NilI)
apply (simp add: Occ_Shift_Nil)
apply (erule notE)
apply (rule singletonI [THEN UN_I])
apply (simp add: Occ_Shift_Nil)
apply (erule notE)
apply (rule singletonI [THEN UN_I])
apply (simp add: Occ_Shift_Nil)
done

lemma Incomparable_Nil_lemma:
  assumes major: "Incomparable(W)"
  and prem: "[]: W"
  and domW: "W <= list(nat)"
  shows "W = {[]}"
apply (insert prem) 
apply (rule equalityI)
prefer 2 apply blast
apply (rule subsetI)
apply (rule_tac P="%x. x: {[]}" in
     major [THEN prem [THEN [3] IncomparableD], THEN subst])
apply (drule_tac c="x" in domW [THEN subsetD])
apply (assumption | rule initseg_NilI singletonI)+
done

lemma Occ_Graft_Occ_cons:
  assumes major: "W ~= {[]}"
  and prem: "Incomparable(W)"
  and domW: "W <= domain(Occ_cons(T, l))"
  and t_tag: "T: Tag"
  and l_list: "l: list(Pow(list(nat)*Tag))"
  and domY: "Y <= list(nat) * Tag"
  shows "Occ_Graft(Occ_cons(T, l), W, Y) =
          Occ_cons(T, mapnth(%z r. Occ_Graft(r, lists_subtree(z, W), Y), l))"
apply (insert t_tag l_list)
apply (subgoal_tac "W <= list(nat)")
prefer 2
apply (insert domW Occ_cons_type [OF t_tag l_list])
apply blast
apply (rule equalityI)
apply (rule_tac [2] subsetI)
apply (rule subsetI)
apply (erule Occ_GraftE)
apply (rule Occ_cons_type [OF t_tag l_list])
apply (erule_tac [3] Occ_consE)
apply (erule_tac [2] Occ_ShiftE)
apply hypsubst
apply (erule Occ_consE)
apply safe
apply (frule_tac [3] domW [THEN subsetD])
apply (safe elim!: Occ_consE)
apply (erule_tac [3]  prem [THEN Incomparable_Nil_lemma,
                       THEN major [THEN notE]])
prefer 3 apply assumption
prefer 3 apply simp
apply (rule Occ_consI2)
apply (simp add: nth_mapnth length_mapnth)
prefer 2 apply (rule Occ_consI1)
prefer 2 apply (rule Occ_consI2)
apply (simp_all add: nth_mapnth length_mapnth)
apply (rule Occ_GraftI1)
apply assumption
apply (rule notI)
apply (elim conjE bexE lists_subtreeE)
apply (drule bspec, assumption)
apply (erule notE)
apply (erule initseg_ConsI, assumption)
apply (rule Occ_GraftI2)
apply (rule_tac [2] Occ_ShiftI)
apply (erule lists_subtreeI)
apply assumption
apply (rule Occ_GraftI1)
apply (rule Occ_consI1)
apply (rule notI)
apply (erule bexE)
apply (erule initseg_NilE)
apply hypsubst
apply (erule prem [THEN Incomparable_Nil_lemma,
                   THEN major [THEN notE]])
apply assumption
apply (erule Occ_GraftE)
apply (rule nth_type2 [THEN PowD], assumption)
apply (erule nat_ltI)
apply (erule length_type)
apply (rule Occ_GraftI1)
apply (erule Occ_consI2)
apply simp
apply (rule notI)
apply (erule bexE)
apply (erule initseg_ConsE)
apply hypsubst
apply (erule prem [THEN Incomparable_Nil_lemma,
                   THEN major [THEN notE]])
apply assumption
apply simp
apply (blast intro: lists_subtreeI)
apply (safe elim!: Occ_ShiftE lists_subtreeE)
apply (simp del: app_Cons add: app_Cons [THEN sym])
apply (rule Occ_GraftI2)
apply (rule_tac [2] Occ_ShiftI)
apply assumption+
done

(** Occ_Graft1 in Occ_range **)
lemma Occ_Graft1_preserves_functionality:
  assumes funcX: "functional(X)"
  and funcY: "functional(Y)"
  and domX: "X <= list(nat)*B"
  and l_list: "l: list(nat)"
  shows "functional(Occ_Graft1(X, l, Y))"
apply (rule functionalI)
apply (erule Occ_Graft1E)
apply (rule domX)
apply (erule_tac [2] Occ_Graft1E)
apply (rule_tac [2] domX)
apply (erule_tac Occ_Graft1E)
apply (rule_tac domX)
apply (safe elim!: Occ_ShiftE)
prefer 4
apply (drule l_list [THEN app_right_inj_iff, THEN iffD1])
apply hypsubst
apply (erule funcY [THEN functionalD])
apply assumption
apply (erule funcX [THEN functionalD])
apply assumption
apply (erule notE)
apply (rule l_list [THEN initseg_appI1])
apply (erule l_list [THEN [2] app_typeD])
apply (erule notE)
apply (rule l_list [THEN initseg_appI1])
apply (erule l_list [THEN [2] app_typeD])
done

lemma Occ_Graft1_preserves_DenseTree:
  assumes hierX: "DenseTree(X)"
  and hierY: "DenseTree(Y)"
  and domX: "X <= list(nat)*B"
  and l_list: "l: domain(X)"
  shows "DenseTree(Occ_Graft1(X, l, Y))"
apply (rule DenseTreeI)
apply (safe elim!: Occ_Graft1E Occ_ShiftE)
apply (erule domX [THEN subsetD])
apply (rule hierX [THEN DenseTreeE])
apply assumption+
apply (rule exI)
apply (erule Occ_Graft1I1)
apply (rule notI)
apply (erule notE)
apply (erule initseg_trans, assumption)
apply (rule l_list [THEN domainE])
apply (erule initseg_right_appE)
apply (erule domX [THEN subsetD, THEN SigmaD1])
apply (rule hierX [THEN DenseTreeE])
apply assumption+
apply (case_tac "m = l")
prefer 2
apply (rule exI)
apply (rule Occ_Graft1I1)
apply assumption
apply (rule notI)
apply (drule initseg_antisym, assumption)
apply (erule notE, assumption)
apply hypsubst
apply (erule hierY [THEN DenseTreeE])
apply (erule initseg_NilI)
apply (rename_tac C)
apply (rule_tac x="C" in exI)
apply (rule_tac P="%x. <x, C>: Occ_Graft1(X, l, Y)" in
         app_right_Nil [THEN subst])
apply (erule domX [THEN subsetD, THEN SigmaD1])
apply (erule Occ_ShiftI [THEN Occ_Graft1I2])
apply hypsubst
apply (erule hierY [THEN DenseTreeE])
apply (erule initseg_appI1)
apply assumption
apply (rule exI)
apply (erule Occ_ShiftI [THEN Occ_Graft1I2])
done

lemma Occ_Graft1_preserves_CorrectArity:
  assumes corrX: "CorrectArity(X, T, n)"
  and corrY: "CorrectArity(Y, T, n)"
  and domX: "X <= list(nat)*B"
  and l_list: "l: domain(X)"
  and domY: "Y <= list(nat)*B"
  and hierY: "DenseTree(Y)"
  and not_emptyY: "Y ~= 0"
  shows "CorrectArity(Occ_Graft1(X, l, Y), T, n)"
apply (subgoal_tac "l: list(nat)")
prefer 2
apply (rule l_list [THEN domainE])
apply (erule domX [THEN subsetD, THEN SigmaD1])
apply (rule CorrectArityI)
apply (erule_tac [2] Occ_Graft1E)
apply (rule_tac [2] domX)
apply (erule Occ_Graft1E)
apply (rule domX)
apply (safe elim!: Occ_ShiftE)
apply (rename_tac l' U)
apply (case_tac "l' @ [m] = l")

prefer 5
apply (frule corrY [THEN CorrectArityD2])
apply assumption
apply (erule notE)
apply (erule Occ_Graft1E)
apply (rule domX)
apply clarify
apply (erule notE)
apply (simp add: app_assoc)
apply (rule initseg_appI1)
apply assumption
apply (erule app_typeD)
apply assumption
apply (erule Occ_ShiftE2)
apply (simp only: app_assoc app_right_inj_iff)
apply (erule exI)

prefer 4
apply (erule Occ_Graft1E)
apply (rule domX)
prefer 2
apply (erule_tac [1] Occ_ShiftE2)
apply (rule_tac [1] app_appE_lemma [THEN bspec, THEN mp, THEN disjE])
prefer 3 apply assumption
apply assumption+
apply (rule l_list [THEN domainE])
apply (erule exE)
apply hypsubst
apply (simp only: app_assoc app_right_inj_iff)
apply (drule app_typeD)
apply assumption
apply (erule_tac a="z" in list.cases)
apply (erule notE)
apply simp
apply (erule initseg_refl)
apply hypsubst
apply simp
apply clarify
apply (erule corrX [THEN CorrectArityD2, THEN notE])
apply assumption
apply (erule exI)
apply (erule exE)
apply hypsubst
apply (erule notE)
apply (drule app_typeD)
apply assumption
apply (erule initseg_appI1)
apply assumption

apply clarify
apply (erule corrX [THEN CorrectArityD2, THEN notE])
apply assumption
apply (erule exI)

prefer 3
apply (erule corrY [THEN CorrectArityD1, THEN exE])
apply assumption
apply (rule exI)
apply (simp add: app_assoc)
apply (erule Occ_ShiftI [THEN Occ_Graft1I2])

prefer 1
apply (rule not_emptyY [THEN not_emptyE])
apply (frule domY [THEN subsetD])
apply (erule SigmaE)
apply hypsubst
apply (erule hierY [THEN DenseTreeE])
apply (erule initseg_NilI)
apply (rename_tac C)
apply (rule_tac x="C" in exI)
apply (erule_tac P="%x. <x, C>: Occ_Graft1(X, l' @ [m], Y)"
        in app_right_Nil [THEN subst])
apply (erule Occ_ShiftI [THEN Occ_Graft1I2])

apply (rule corrX [THEN CorrectArityD1, THEN exE])
apply assumption+
apply (rule exI)
apply (erule Occ_Graft1I1)
apply (rule notI)
apply (erule notE)
apply (erule initseg_right_appE)
apply assumption+
apply (rename_tac m' y)
apply (erule_tac a="m'" in list.cases)
apply simp
apply simp
done

lemma Occ_shift_in_fin_bnd_set:
  assumes prem1: "X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  and prem2: "b: nat"
  shows "Occ_shift(b, X) : fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
apply (rule Occ_fbs_op_bnd_mono [THEN fin_bnd_set_succI])
apply (rule_tac [2] prem1)
apply (insert prem1 [THEN fin_bnd_set_domain [THEN subsetD], THEN PowD])
apply (unfold Occ_fbs_op_def Occ_fbs_dom_def list_dom_def list_op_def)
apply (rule subsetI)
apply (erule Occ_shiftE)
apply hypsubst
apply (drule subsetD, assumption)
apply (erule SigmaE2)
apply (rule SigmaI)
prefer 2 apply assumption
apply (rule CollectI)
prefer 2 apply (rule disjI2)
apply (intro exI conjI)
apply (rule refl)
apply (rule prem2)
apply (erule domainI)
apply (unfold list.con_defs)
apply (erule prem2 [THEN A_subset_univ [THEN subsetD],
                    THEN Pair_in_univ, THEN Inr_in_univ])
done

lemma Occ_Shift_in_fin_bnd_set:
  assumes prem1: "X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  and prem2: "l: list(nat)"
  shows "Occ_Shift(l, X) : fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
apply (unfold Occ_fbs_dom_def)
apply (rule prem2 [THEN list.induct])
apply (rule prem1 [unfolded Occ_fbs_dom_def,
                   THEN fin_bnd_set_domain [THEN subsetD],
                   THEN PowD, THEN Occ_Shift_Nil, THEN ssubst])
apply (rule prem1 [unfolded Occ_fbs_dom_def])
apply (simp add: Occ_Shift_Cons)
apply (fold Occ_fbs_dom_def)
apply (erule Occ_shift_in_fin_bnd_set)
apply assumption
done

lemma Occ_Graft1_in_fin_bnd_set:
  assumes prem1: "X: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  and prem2: "Y: fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
  and l_list: "l: list(nat)"
  shows "Occ_Graft1(X, l, Y):
                 fin_bnd_set(Occ_fbs_dom(Tag), Occ_fbs_op(Tag))"
apply (unfold Occ_Graft1_def)
apply (rule Occ_fbs_op_bnd_mono [THEN fin_bnd_set_UnI])
apply (rule fin_bnd_set_subsetI
        [OF Occ_fbs_op_bnd_mono Diff_subset prem1])
apply (rule Occ_Shift_in_fin_bnd_set [OF prem2 l_list])
done

lemma Occ_Graft1_not_empty:
  assumes domY: "Y <= list(nat) * B"
  and not_emptyY: "Y ~= 0"
  shows "Occ_Graft1(X, l, Y) ~= 0"
apply (rule not_emptyY [THEN not_emptyE])
apply (frule domY [THEN subsetD])
apply (erule SigmaE)
apply hypsubst
apply (rule not_emptyI)
apply (erule Occ_ShiftI [THEN Occ_Graft1I2])
done

lemma Occ_Graft1_in_Occ_range:
  assumes domX: "X: Occ_range(Tag, Arity)"
  and domY: "Y: Occ_range(Tag, Arity)"
  and l_list: "l: domain(X)"
  shows "Occ_Graft1(X, l, Y): Occ_range(Tag, Arity)"
apply (subgoal_tac "X <= list(nat) * Tag"
                   "Y <= list(nat) * Tag" "l: list(nat)")
prefer 2
apply (rule l_list [THEN domainE])
apply (erule subsetD [THEN SigmaD1])
apply assumption
prefer 2
apply (rule domY [THEN Occ_rangeE])
apply (erule Occ_fbs_op_lfp_lowerbound)
prefer 2
apply (rule domX [THEN Occ_rangeE])
apply (erule Occ_fbs_op_lfp_lowerbound)

apply (rule domX [THEN Occ_rangeE])
apply (rule domY [THEN Occ_rangeE])
apply (insert l_list)
apply (rule Occ_rangeI)
apply (rule_tac [5] ballI)
apply (drule_tac [5] bspec)
apply (drule_tac [6] bspec)
apply (assumption
       | rule Occ_Graft1_in_fin_bnd_set
              Occ_Graft1_not_empty
              Occ_Graft1_preserves_functionality
              Occ_Graft1_preserves_DenseTree
              Occ_Graft1_preserves_CorrectArity)+
done

lemma Occ_Graft_in_Occ_range:
  assumes finW: "W: Fin(list(nat))"
  and prem: "Incomparable(W)"
  and domW: "W <= domain(X)"
  and domX: "X: Occ_range(Tag, Arity)"
  and domY: "Y: Occ_range(Tag, Arity)"
  shows "Occ_Graft(X, W, Y): Occ_range(Tag, Arity)"
apply (rule domW [THEN rev_mp])
apply (rule prem [THEN rev_mp])
apply (rule finW [THEN Fin_induct])
apply (intro impI)
apply (rule Occ_Graft_0 [THEN ssubst])
apply (rule domX)

apply (intro impI)
apply (rule Occ_Graft_cons [THEN ssubst])
prefer 5
apply (rule Occ_Graft1_in_Occ_range)
apply (subgoal_tac "x ~: y ==> y - {x} = y")
prefer 2 apply blast
apply simp
apply (erule mp)
apply (erule Incomparable_subset)
apply blast
apply (rule domY)

apply (erule cons_subsetE)
apply (erule domainE)
apply (rule domainI)
apply (rule Occ_GraftI1)
apply assumption
apply (rule notI)
apply (erule bexE)
apply (erule DiffE)
apply (drule IncomparableD)
apply assumption
apply (erule consI2)
apply (rule consI1)
apply hypsubst
apply (erule singletonI [THEN [2] notE])

apply assumption+
apply (rule domX [THEN Occ_rangeE])
apply (erule Occ_fbs_op_lfp_lowerbound)
apply (rule domY [THEN Occ_rangeE])
apply (erule Occ_fbs_op_lfp_lowerbound)
done

lemma Occ_Graft_in_Occ_range2:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and prem: "Incomparable(W)"
  and domW: "W <= domain(X)"
  and domX: "X: Occ_range(Tag, Arity)"
  and domY: "Y: Occ_range(Tag, Arity)"
  shows "Occ_Graft(X, W, Y): Occ_range(Tag, Arity)"
apply (rule Occ_Graft_in_Occ_range)
apply (rule domW [THEN Fin_subset])
apply (rule Fin_domainI)
apply (rule Occ_range_convert_lemma [OF hcons domX])
apply (erule hind [THEN Occ_ind_cond_Occ_FinI])
apply (assumption | rule prem domW domX domY)+
done


(** subst **)
lemma def_graft_type:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and hsubst: "!!x W y. graft(x, W, y) == Occinv(Occ_Graft(Occ(x), W, Occ(y)))"
  shows
   "[|
        M: Terms; N: Terms;
        Incomparable(W); W <= domain(Occ(M))
    |] ==> graft(M, W, N): Terms"
apply (unfold hsubst)
apply (rule def_Occinv_type [OF hcons hind hinv])
apply (rule Occ_Graft_in_Occ_range2 [OF hcons hind])
apply (assumption | rule hind [THEN Occ_ind_cond_Occ_in_Occ_range])+
done

lemma def_graft_0:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and hsubst: "!!x W y. graft(x, W, y) == Occinv(Occ_Graft(Occ(x), W, Occ(y)))"
  and prem: "M: Terms"
  shows "graft(M, 0, N) = M"
apply (unfold hsubst)
apply (insert prem)
apply (simp only: def_Occinv_Occ [OF hcons hind hinv] Occ_Graft_0) 
done

lemma def_graft_Nil:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and hsubst: "!!x W y. graft(x, W, y) == Occinv(Occ_Graft(Occ(x), W, Occ(y)))"
  shows
   "[| M: Terms; N: Terms
    |] ==> graft(M, {[]}, N) = N"
apply (unfold hsubst)
apply (subgoal_tac "Occ(M) <= list(nat) * Tag"
                   "Occ(N) <= list(nat) * Tag")
apply (simp only: def_Occinv_Occ [OF hcons hind hinv] Occ_Graft_Nil)
apply (assumption | rule hind [THEN Occ_ind_cond_Occ_domain])+
done

lemma def_graft:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinj: "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and hsubst: "!!x W y. graft(x, W, y) == Occinv(Occ_Graft(Occ(x), W, Occ(y)))"
  shows
   "[|
        Term_cons(T, l): Terms;
        T: Tag; l: list(Terms); Arity(T) = length(l); y: Terms;
        W ~= {[]}; Incomparable(W);
        W <= domain(Occ(Term_cons(T, l)))
    |] ==> graft(Term_cons(T, l), W, y) = 
         Term_cons(T, mapnth(%z r. graft(r, lists_subtree(z, W), y), l))"
apply (unfold hsubst)
apply (subgoal_tac "map(Occ, l): list(Pow(list(nat) * Tag))"
                   "Arity(T) = length(map(Occ, l))"
                   "Occ(y) <= list(nat) * Tag"
                   "Occ_Graft(Occ(Term_cons(T, l)), W, Occ(y))
                       : Occ_range(Tag, Arity)")
apply (simp add: Occ_Term_cons [OF hind hinj]
           Occ_Graft_Occ_cons mapnth_map)
apply (rule def_Occinv2 [OF hcons hind hinv, THEN trans])
prefer 5 apply (simp add: map_mapnth)
prefer 4 apply (simp add: length_mapnth)
prefer 6 apply simp
prefer 3
apply (rule nth_convert_list_type)
apply (erule mapnth_type2)
apply (simp add: nth_mapnth length_mapnth)
apply (rule ballI)
apply (rule Occ_Graft_domain)
apply (rule hind [THEN Occ_ind_cond_Occ_domain])
apply simp
apply assumption

prefer 5 apply (erule hind [THEN Occ_ind_cond_Occ_domain])
prefer 3 apply assumption
prefer 4 apply (erule map_type)
apply (erule hind [THEN Occ_ind_cond_Occ_domain, THEN PowI])
prefer 3 apply (rule Occ_Graft_in_Occ_range2 [OF hcons hind])
apply assumption+
apply (erule hind [THEN Occ_ind_cond_Occ_in_Occ_range])+
prefer 2 apply simp

apply (rule_tac P="%x. lists_subtree(z, W) <= x" in subst)
apply (erule_tac [2] lists_subtree_mono)
apply (simp add: lists_subtree_domain_eq Occ_subtree_Occ_cons nth_map)
done

end
