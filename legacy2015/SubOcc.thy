(*
    File:        SubOcc.thy
    Time-stamp:  <2015-12-23T12:46:41Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory SubOcc imports OccTools begin

definition Occ_Subtree :: "[i, i] => i" where
"Occ_Subtree(m, X) == {z. y: X, EX l T. z = <l, T> & y = <m@l, T>}"

definition Term_cons_inj_cond :: "[i, i, i=>i, [i,i]=>i]=>o" where
  "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)
        == ALL T: Tag. ALL U: Tag. ALL l: list(Terms). ALL m: list(Terms).
              Term_cons(T, l): Terms -->
           (Term_cons(T, l) = Term_cons(U, m) <-> T = U &
                 (ALL z: Arity(T). nth(z, l) = nth(z, m)))"

(** Occ_Subtree **)
lemma Occ_SubtreeI:
  "[| m: list(A); <m@l, T>: X |] ==> <l, T>: Occ_Subtree(m, X)"
apply (unfold Occ_Subtree_def)
apply (rule ReplaceI)
prefer 2 apply assumption
apply (rule refl conjI exI)+
apply (elim conjE exE)
apply simp
done

lemma Occ_SubtreeD:
  "<l, T>: Occ_Subtree(m, X) ==> <m@l, T>: X"
apply (unfold Occ_Subtree_def)
apply blast
done

lemma Occ_SubtreeE:
  "[| x: Occ_Subtree(m, X);
      !!l T. [| x = <l, T>; <m@l, T>: X |] ==> R |]==> R"
apply (unfold Occ_Subtree_def)
apply blast
done

lemma Occ_SubtreeE2:
  "[| <l, T>: Occ_Subtree(m, X);
      <m@l, T>: X ==> R |] ==> R"
apply (unfold Occ_Subtree_def)
apply blast
done

lemma Occ_Subtree_0:
  "Occ_Subtree(m, 0) = 0"
apply (unfold Occ_Subtree_def)
apply blast
done

lemma Occ_Subtree_Nil:
  "X <= A * B ==> Occ_Subtree([], X) = X"
apply (unfold Occ_Subtree_def)
apply simp
apply blast
done

lemma Occ_Subtree_Cons:
  "l: list(A) ==>
      Occ_Subtree(Cons(a, l), X) = Occ_Subtree(l, Occ_subtree(a, X))"
apply (unfold Occ_Subtree_def)
apply simp
apply (rule equalityI)
apply (safe elim!: Occ_subtreeE)
apply (rule ReplaceI)
apply (erule_tac [2] Occ_subtreeI)
apply (rule_tac [3] ReplaceI)
prefer 4 apply assumption
prefer 3
apply (assumption | rule refl exI conjI)+
apply (elim exE conjE)
apply simp
apply (elim exE conjE)
apply simp
done

lemma Occ_Subtree_app:
  assumes prem1: "l: list(A)"
  and prem2: "m: list(A)"
  and prem3: "X <= list(C) * D"
  shows "Occ_Subtree(l@m, X) = Occ_Subtree(m, Occ_Subtree(l, X))"
apply (rule prem3 [THEN rev_mp])
apply (rule_tac x="X" in spec)
apply (insert prem2)
apply (rule prem1 [THEN list.induct])
apply (simp_all add: Occ_Subtree_Nil Occ_Subtree_Cons)
apply (intro impI allI)
apply (drule Occ_subtree_preserves_domain)
apply (drule spec)
apply (drule mp, assumption)
apply assumption
done

lemma Occ_Subtree_in_Occ_range:
  assumes major: "<l, T>: X"
  and prem: "X: Occ_range(Tag, Arity)"
  shows "Occ_Subtree(l, X): Occ_range(Tag, Arity)"
apply (rule prem [THEN rev_mp])
apply (rule major [THEN rev_mp])
apply (rule_tac x="X" in spec)
apply (rule list.induct
    [OF major [THEN prem
       [THEN Occ_range_domain_lemma, THEN subsetD, THEN SigmaD1]]])
apply (intro impI allI)
apply (frule Occ_range_domain_lemma)
apply (simp add: Occ_Subtree_Nil)
apply (intro impI allI)
apply (frule Occ_range_domain_lemma)
apply (simp add: Occ_Subtree_Cons)
apply (erule spec [THEN mp, THEN mp])
apply (erule Occ_subtreeI)
apply (rule Occ_subtree_in_Occ_range)
apply assumption+
done


(** Term_cons_inj_cond **)
lemma Term_cons_inj_condI:
  assumes 
  "!! T U l m.
    [| T: Tag; U: Tag; l: list(Terms); m: list(Terms);
      Term_cons(T, l): Terms
    |] ==> Term_cons(T, l) = Term_cons(U, m) <->
          T = U & (ALL z: Arity(T). nth(z, l) = nth(z, m))"
  shows "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)"
apply (unfold Term_cons_inj_cond_def)
apply (assumption | rule assms ballI impI)+
done

lemma Term_cons_inj_condD:
  "[| Term_cons_inj_cond(Terms, Tag, Arity, Term_cons);
      T: Tag; U: Tag; l: list(Terms); m: list(Terms);
      Term_cons(T, l): Terms
   |] ==> Term_cons(T, l) = Term_cons(U, m) <->
           T = U & (ALL z: Arity(T). nth(z, l) = nth(z, m))"
apply (unfold Term_cons_inj_cond_def)
apply blast
done

lemma Term_cons_inj_condD1:
  "[| Term_cons_inj_cond(Terms, Tag, Arity, Term_cons);
      Term_cons(T, l) = Term_cons(U, m);
      T: Tag; U: Tag; l: list(Terms); m: list(Terms);
      Term_cons(T, l): Terms
   |] ==> T = U & (ALL z: Arity(T). nth(z, l) = nth(z, m))"
apply (unfold Term_cons_inj_cond_def)
apply blast
done

lemma Occ_ind_cond_Term_cons_lemma:
  "[| Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons);
      M: Terms |] ==> EX T: Tag. EX l: list(Terms).
          M = Term_cons(T, l) & Arity(T) = length(l)"
apply (erule Occ_ind_condD)
apply (assumption | rule refl bexI conjI)+
done

lemma Term_cons_inj_cond_induct_lemma:
  assumes hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinj: "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)"
  and major: "M: Terms"
  and indstep:
     "!! l T. [| T: Tag; l: list(Terms);
            Term_cons(T, l): Terms;
            Arity(T) = length(l);
            Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l));
            ALL z: length(l). ALL U: Tag. ALL m: list(Terms).
               nth(z, l) = Term_cons(U, m) & Arity(U) = length(m)
               --> P(nth(z, l), U, m)
      |]  ==> P(Term_cons(T, l), T, l)"
  shows 
    "ALL T. ALL l. M = Term_cons(T, l) & Arity(T) = length(l) &
          T: Tag & l: list(Terms) --> P(M, T, l)"
apply (rule Occ_ind_condD [OF hind major])
apply (intro impI allI)
apply (elim conjE)
apply (drule hinj [THEN Term_cons_inj_condD1])
apply assumption+
apply (erule conjE)
apply hypsubst
apply (rename_tac m)
apply (subgoal_tac "l = m")
prefer 2
apply (rule nth_inj)
apply simp
apply simp
apply assumption+
apply hypsubst
apply (rule indstep)
apply assumption+
apply (intro ballI impI)
apply (erule conjE)
apply (drule bspec)
apply assumption
apply (drule spec [THEN spec, THEN mp])
apply (assumption | rule conjI)+
done

lemma Term_cons_inj_cond_induct:
  assumes hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinj: "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)"
  and major: "Term_cons(T, l): Terms"
  and t_tag: "T: Tag"
  and l_list: "l: list(Terms)"
  and lencond: "Arity(T) = length(l)"
  and indstep:
     "!! l T. [| T: Tag; l: list(Terms);
          Term_cons(T, l): Terms;
          Arity(T) = length(l);
          Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l));
          ALL z: length(l). ALL U: Tag. ALL m: list(Terms).
             nth(z, l) = Term_cons(U, m) & Arity(U) = length(m)
               --> P(U, m)
      |]  ==> P(T, l)"
  shows "P(T, l)"
apply (rule Term_cons_inj_cond_induct_lemma [OF hind hinj major,
         THEN spec, THEN spec, THEN mp])
prefer 2
apply (assumption | rule refl t_tag l_list lencond conjI)+
apply (rule indstep)
apply assumption+
done

lemma Occ_Term_cons:
  assumes hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinj: "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)"
  and major: "Term_cons(T, l): Terms"
  and t_tag: "T: Tag"
  and l_list: "l: list(Terms)"
  and lencond: "Arity(T) = length(l)"
  shows "Occ(Term_cons(T, l)) = Occ_cons(T, map(Occ, l))"
apply (rule Term_cons_inj_cond_induct [OF hind hinj major t_tag l_list lencond])
apply assumption
done

lemma def_Sub_type:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and hsub: "!!M. Sub(M) == {<l, Occinv(Occ_Subtree(l, Occ(M)))>. <l, T>: Occ(M)}"
  and major: "M: Terms"
  shows "Sub(M) <= list(nat)*Terms"
apply (unfold hsub)
apply safe
apply (frule Occ_ind_cond_Occ_domain [OF hind major, THEN subsetD])
apply (erule SigmaE)
apply hypsubst
apply simp
apply (insert major)
apply (blast intro: def_Occinv_type [OF hcons hind hinv]
               Occ_Subtree_in_Occ_range
               hind [THEN Occ_ind_cond_Occ_in_Occ_range])
done

lemma def_Sub_rec:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and hsub: "!!M. Sub(M) == {<l, Occinv(Occ_Subtree(l, Occ(M)))>. <l, T>: Occ(M)}"
  and hinj: "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)"
  and major: "Term_cons(T, l): Terms"
  and t_tag: "T: Tag"
  and l_list: "l: list(Terms)"
  and lencond: "Arity(T) = length(l)"
  shows "Sub(Term_cons(T, l)) = Occ_cons(Term_cons(T, l), map(Sub, l))"
apply (unfold hsub)
apply (rule Term_cons_inj_cond_induct [OF hind hinj major t_tag l_list lencond])
apply (rule equalityI)
apply safe
apply (frule hind [THEN Occ_ind_cond_Occ_domain])
apply (frule subsetD)
apply assumption
apply (erule SigmaE)
apply hypsubst
apply simp
apply (rename_tac v y)
apply (rule_tac a="v" in list.cases)
apply assumption
apply hypsubst
apply (drule_tac a="Occ(Term_cons(T, l))" in sym)
apply (simp add: def_Occinv_Occ [OF hcons hind hinv]
         Occ_Subtree_Nil)
apply (rule Occ_consI1)
apply simp
apply (erule Occ_cons_ConsE)
apply (subgoal_tac "map(Occ, l): list(Pow(list(nat) * Tag))")
apply (simp add: Occ_subtree_Occ_cons Occ_Subtree_Cons)
apply (rule Occ_consI2)
apply simp
apply (simp add: nth_map)
apply (unfold hsub)
apply (rule RepFun_eqI)
prefer 2 apply assumption
apply simp
apply (erule map_type)
apply (erule hind [THEN Occ_ind_cond_Occ_domain, THEN PowI])

apply (erule Occ_consE)
apply hypsubst
apply (rule RepFun_eqI)
prefer 2
apply simp
apply (rule Occ_consI1)
apply (frule hind [THEN Occ_ind_cond_Occ_domain])
apply (drule_tac a="Occ(Term_cons(T, l))" in sym)
apply (simp add: def_Occinv_Occ [OF hcons hind hinv]
              Occ_Subtree_Nil)
apply hypsubst
apply (simp add: nth_map)
apply (erule bexE)
apply (subgoal_tac "nth(a, l): Terms")
apply (frule_tac M="nth(a, l)" in hind [THEN Occ_ind_cond_Occ_domain])
apply (drule subsetD, assumption)
apply (erule SigmaE)
apply hypsubst
apply simp
apply (rename_tac n y)
apply (rule_tac x="<Cons(a, n), y>" in bexI)
apply (rule_tac [2] Occ_consI2)
apply (subgoal_tac "a: nat" "map(Occ, l): list(Pow(list(nat) * Tag))")
apply (simp add: nth_map Occ_subtree_Occ_cons Occ_Subtree_Cons)
apply (erule map_type)
apply (erule hind [THEN Occ_ind_cond_Occ_domain, THEN PowI])
apply (erule mem_nat_in_nat)
apply (erule length_type)
apply simp
apply (simp add: nth_map)
apply (rule nth_type2)
apply assumption
apply (erule ltI)
apply (erule length_type [THEN nat_into_Ord])
done

lemma def_Sub_functional:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and hsub: "!!M. Sub(M) == {<l, Occinv(Occ_Subtree(l, Occ(M)))>. <l, T>: Occ(M)}"
  and hinj: "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)"
  and major: "M: Terms"
  shows "functional(Sub(M))"
apply (rule Occ_ind_condD [OF hind major])
apply (simp add: def_Sub_rec [OF hcons hind hinv hsub hinj])
apply (rule functionalI)
apply (elim Occ_consE)
apply (simp_all add: nth_map)
apply clarify
apply (drule bspec)
apply (erule_tac [2] functionalD)
apply assumption+
done

lemma def_subterm_Nil:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and hsub: "!!M. Sub(M) == {<l, Occinv(Occ_Subtree(l, Occ(M)))>. <l, T>: Occ(M)}"
  and hinj: "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)"
  and hsubterm: "!!M l. subterm(M, l) == THE N. <l, N>: Sub(M)"
  and major: "M: Terms"
  shows "subterm(M, []) = M"
apply (unfold hsubterm)
apply (subgoal_tac "<[], M>: Sub(M)")
apply (rule the_equality)
apply assumption
apply (rule def_Sub_functional [OF hcons hind hinv hsub hinj major,
                                THEN functionalD])
apply assumption+
apply (rule Occ_ind_condD [OF hind major])
apply (simp add: def_Sub_rec [OF hcons hind hinv hsub hinj])
apply (rule Occ_consI1)
done

lemma def_subterm_Cons:
  assumes hcons: "Occ_cons_cond(Terms, Occ, Tag, Arity)"
  and hind: "Occ_ind_cond(Terms, Occ, Tag, Arity, Term_cons)"
  and hinv: "!!x. Occinv(x) == THE M. M: Terms & x = Occ(M)"
  and hsub: "!!M. Sub(M) == {<l, Occinv(Occ_Subtree(l, Occ(M)))>. <l, T>: Occ(M)}"
  and hinj: "Term_cons_inj_cond(Terms, Tag, Arity, Term_cons)"
  and hsubterm: "!!M l. subterm(M, l) == THE N. <l, N>: Sub(M)"
  and major: "Term_cons(T, l): Terms"
  and t_tag: "T: Tag"
  and l_list: "l: list(Terms)"
  and hlen: "Arity(T) = length(l)"
  and prem1: "m: list(nat)"
  and prem2: "a: length(l)"
  shows "subterm(Term_cons(T, l), Cons(a, m)) = subterm(nth(a, l), m)"
apply (unfold hsubterm)
apply (insert major t_tag l_list hlen prem1 prem2)
apply (simp add: def_Sub_rec [OF hcons hind hinv hsub hinj])
apply (subgoal_tac "nth(a, l): Terms")
prefer 2
apply (rule nth_type2, assumption)
apply (erule ltI)
apply (erule length_type [THEN nat_into_Ord])
apply (case_tac "EX X. <m, X>: Sub(nth(a, l))")
prefer 2
apply (rule the_0 [THEN sym, THEN [2] trans])
prefer 2
apply (rule notI)
apply (erule notE)
apply blast
apply (rule the_0)
apply (rule notI)
apply (erule notE)
apply (erule ex1E)
apply (erule Occ_cons_ConsE)
apply (rule exI)
apply (simp add: nth_map)
apply (rule the_equality)
apply (rule_tac [2] the_equality [THEN sym])
apply (erule_tac [3] Occ_cons_ConsE)
apply (erule_tac [2] Occ_cons_ConsE)
apply (rule Occ_consI2)
apply (simp_all add: nth_map)
prefer 2
apply (rule def_Sub_functional [OF hcons hind hinv hsub hinj,
                                THEN functionalD])
prefer 2 apply assumption
prefer 2 apply assumption
apply simp
apply (rule theI)
apply (erule exE)
apply (rule ex1I)
apply assumption
apply (rule def_Sub_functional [OF hcons hind hinv hsub hinj,
                                THEN functionalD])
prefer 2 apply assumption
apply simp
apply assumption
done

end
