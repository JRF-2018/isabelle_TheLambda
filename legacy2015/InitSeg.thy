(*
    File:        InitSeg.thy
    Time-stamp:  <2015-12-26T12:09:01Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory InitSeg imports Nth Poset begin

definition initseg :: "[i,i,i]=>o" where
"initseg(A, l, m) == l: list(A) & m: list(A) &   
                  (EX x: list(A). l@x = m)"

lemma app_typeD:
    "[| l @ m: list(A); l: list(A) |] ==> m: list(A)"
apply (erule rev_mp)
apply (erule list.induct)
apply simp_all
done

lemma app_Un_type:
  "!! a b. [| a: list(A); b: list(B) |] ==> a @ b: list(A Un B)"
apply (rule app_type)
apply (erule Un_upper1 [THEN list_mono, THEN subsetD])
apply (erule Un_upper2 [THEN list_mono, THEN subsetD])
done

lemma app_right_inj:
    "[| l@m = l@n; l: list(A) |] ==> m = n"
apply (erule rev_mp)
apply (erule list.induct)
apply simp_all
done

lemma app_right_inj_iff:
    "l: list(A) ==> l@m = l@n <-> m = n"
apply (rule iffI)
apply (erule app_right_inj, assumption)
apply (erule subst)
apply (rule refl)
done

lemma app_last_eqD:
  assumes major: "l @ [a] = m @ [b]"
  and prem1: "l: list(A)"
  and prem2: "m: list(B)"
  shows "l = m & a = b"
apply (rule major [THEN rev_mp])
apply (rule prem2 [THEN rev_bspec])
apply (rule prem1 [THEN list.induct])
apply (rule ballI)
apply (rule_tac [2] ballI)
apply (erule_tac [2] a="x" in list.cases)
apply (erule_tac [1] a="x" in list.cases)
apply (erule_tac [3] a="l" in list.cases)
apply (erule_tac [2] a="l" in list.cases)
apply simp_all
apply (rule impI)
apply (erule bspec [THEN mp], assumption)
apply (erule conjE)
apply assumption
done

lemma app_last_iff:
    "!!l m. [| l: list(A); m: list(B) |] ==> 
           l @ [a] = m @ [b] <-> l = m & a = b"
apply (blast dest!: app_last_eqD)
done

lemma app_left_inj:
  assumes prem: "a@c = b@c"
  and major: "a: list(A)"
  and prem1: "b: list(B)"
  and prem2: "c: list(C)"
  shows "a = b"
apply (rule prem [THEN rev_mp])
apply (rule prem1 [THEN rev_bspec])
apply (rule major [THEN rev_bspec])
apply (rule prem2 [THEN list_append_induct])
apply simp
apply clarify
apply (simp only: app_assoc [THEN sym])
apply (blast dest!: app_last_eqD intro!: app_Un_type)
done

lemma app_left_inj_iff:
  "[| a: list(A); b: list(A); c: list(A) |] ==> a@c = b@c <-> a = b"
apply (rule iffI)
apply (erule app_left_inj, assumption+)
apply (erule subst)
apply (rule refl)
done

lemma app_appE_lemma:
    "m: list(A) ==> ALL l: list(A). m @ x = l @ y --> 
          (EX z. l = m @ z) | (EX z. m = l @ z)"
apply (erule list.induct)
apply simp_all
apply (intro ballI impI)
apply (rename_tac v)
apply (erule_tac a="v" in list.cases)
apply simp_all
done

lemma app_appE:
  assumes major: "m @ x = l @ y"
  and m_list: "m: list(A)"
  and l_list: "l: list(A)"
  and prem1: "!! z. [| z: list(A); l = m @ z; x = z @ y |] ==> R"
  and prem2: "!! z. [| z: list(A); m = l @ z; y = z @ x |] ==> R"
  shows "R"
apply (insert m_list l_list major)
apply (rule m_list [THEN app_appE_lemma, THEN bspec, THEN mp, THEN disjE])
apply (rule l_list)
apply (rule major)
apply (erule exE)
apply (erule_tac [2] exE)
apply (rule_tac [2] prem2)
apply (rule prem1)
apply hypsubst
apply (erule app_typeD)
apply assumption+
prefer 2 apply hypsubst
apply (erule app_typeD)
apply assumption
prefer 2 apply assumption
apply (simp_all add: app_assoc app_right_inj_iff)
done

lemma app_Nil_eqD1:
  assumes major: "a@b = a"
  and prem: "a:list(A)"
  shows "b = []"
apply (rule major [THEN rev_mp])
apply (rule prem [THEN list.induct])
apply simp_all
done

lemma app_Nil_eqD2:
  assumes major: "a@b = b"
  and prem1: "a: list(A)"
  and prem2: "b: list(B)"
  shows "a = []"
apply (rule major [THEN rev_mp])
apply (rule prem1 [THEN rev_bspec])
apply (rule prem2 [THEN list_append_induct])
apply simp
apply (intro ballI impI)
apply (simp only: app_assoc [THEN sym])
apply (blast dest!: app_last_eqD intro: app_Un_type)
done

lemma app_eq_Nil_iff:
    "a: list(A) ==> a @ b = [] <-> a = [] & b = []"
apply (erule list.induct)
apply simp_all
done

lemma app_eq_NilD:
  "[| a @ b = []; a: list(A) |] ==> a = [] & b = []"
apply (rule app_eq_Nil_iff [THEN iffD1])
apply assumption+
done

lemma app_antisym:
    "[| a @ c = b; b @ d = a; 
       a: list(A); b: list(B); c: list(C); d:list(D) 
     |] ==> a = b"
apply hypsubst
apply (simp add: app_assoc)
done

lemma app_antisym2:
    "[| c @ a = b; d @ b = a;
      a: list(A); b: list(B); c: list(C); d:list(D)
     |] ==> a = b"
apply hypsubst
apply (simp only: app_assoc [THEN sym])
apply (safe dest!: app_Nil_eqD2 app_eq_NilD)
apply (assumption | (rule app_Un_type))+
apply simp
done

(** initseg **)
lemma initsegI:
  "!!a. [| a@x = b; x: list(A); a: list(A); b: list(A) |]
         ==> initseg(A, a, b)"
apply (unfold initseg_def)
apply blast
done

lemma initsegD1:
    "initseg(A, a, b) ==> a: list(A)"
apply (unfold initseg_def)
apply blast
done

lemma initsegD2:
    "initseg(A, a, b) ==> b: list(A)"
apply (unfold initseg_def)
apply blast
done

lemma initsegE:
    "[| initseg(A, a, b);
       !!x. [| a: list(A); b: list(A); x: list(A); b = a@x |] ==> R
     |] ==> R"
apply (unfold initseg_def)
apply blast
done

lemma initseg_antisym:
    "[| initseg(A, x, y); initseg(A, y, x) |] ==> x = y"
apply (unfold initseg_def)
apply (elim conjE bexE)
apply (erule app_antisym, assumption)
apply assumption+
done

lemma initseg_trans:
  "[| initseg(A, x, y); initseg(A, y, z) |] ==> initseg(A, x, z)"
apply (unfold initseg_def)
apply clarify
apply (simp add: app_assoc)
done

lemma initseg_refl:
    "x: list(A) ==> initseg(A, x, x)"
apply (unfold initseg_def)
apply simp
done

lemma initseg_appI1:
    "[| x: list(A); y: list(A) |] ==> initseg(A, x, x@y)"
apply (unfold initseg_def)
apply simp
done

lemma initseg_appI2:
    "[| x: list(A); initseg(A, y, z) |] ==> initseg(A, x@y, x@z)"
apply (unfold initseg_def)
apply (elim conjE bexE)
apply (rule conjI)
apply simp
apply (rule conjI)
apply simp
apply hypsubst
apply (simp add: app_assoc)
done

lemma initseg_NilI:
    "x: list(A) ==> initseg(A, [], x)"
apply (unfold initseg_def)
apply simp
done

lemma initseg_ConsI:
  "[| a: A; initseg(A, y, z) |] ==> initseg(A, Cons(a, y), Cons(a, z))"
apply (unfold initseg_def)
apply (elim conjE bexE)
apply (assumption | rule conjI list.intros)+
apply hypsubst
apply (rule bexI)
apply (rule app_Cons)
apply assumption
done

lemma initseg_NilE:
    "[| initseg(A, l, []); l = [] ==> R |] ==> R"
apply (unfold initseg_def)
apply (elim conjE bexE)
apply (blast dest!: app_eq_NilD)
done

lemma initseg_ConsE:
  assumes major: "initseg(A, l, Cons(b, m))"
  and nil_case: "l = [] ==> R"
  and cons_case: "!!n. [| initseg(A, n, m); b: A; l = Cons(b, n) |] ==> R"
  shows "R"
apply (insert major)
apply (unfold initseg_def)
apply (elim conjE bexE)
apply (erule list.cases)
apply (erule nil_case)
apply (rule cons_case [unfolded initseg_def])
apply (erule_tac [2] ConsE)
prefer 2 apply assumption
prefer 2 apply hypsubst
apply simp
apply hypsubst
apply (erule ConsE)
apply simp
apply (rule bexI)
apply (erule conjunct2)
apply assumption
done

lemma initseg_left_ConsE:
  assumes major: "initseg(A, Cons(b, l), m)"
  and prem: "!!n. [| m = Cons(b, n); b: A; initseg(A, l, n) |] ==>R"
  shows "R"
apply (insert major)
apply (unfold initseg_def)
apply (elim conjE bexE)
apply simp
apply (erule sym [THEN prem [unfolded initseg_def]])
apply safe
apply (assumption | rule app_type refl bexI)+
done

lemma initseg_left_appE:
  assumes major: "initseg(A, a@b, c)"
  and prem1: "a: list(A)"
  and prem2: "!!l. [| c = a@l; initseg(A, b, l) |] ==>R"
  shows "R"
apply (insert major prem1)
apply (unfold initseg_def)
apply (elim conjE bexE)
apply (drule app_typeD, assumption)
apply (simp add: app_assoc)
apply (erule sym [THEN prem2 [unfolded initseg_def]])
apply (assumption | rule conjI app_type refl bexI)+
done

lemma initseg_right_appE:
  assumes major: "initseg(A, l, m@n)"
  and m_list: "m: list(A)"
  and prem1: "[| n: list(A); initseg(A, l, m) |] ==> R"
  and prem2: "!!x y. [| x: list(A); y: list(A); n: list(A); l = m @ x; n = x @ y;
                  initseg(A, m, l) |] ==> R"
  shows "R"
apply (insert m_list)
apply (rule major [THEN initsegE])
apply (subgoal_tac "n: list(A)")
prefer 2 apply (erule app_typeD, assumption)
apply (rule app_appE_lemma [THEN bspec, THEN mp, THEN disjE])
prefer 3 apply assumption
apply assumption+
apply (erule_tac [2] exE)
apply (erule exE)
apply (rule_tac [2] prem1)
apply (rule_tac [1] prem2)
prefer 4 apply assumption
apply (simp_all add: app_right_inj_iff app_assoc)
apply (assumption | (erule app_typeD, assumption)
        | (rule initseg_appI1))+
done

lemma initseg_app_lastE:
  assumes major: "initseg(A, l, m@[b])"
  and prem: "m: list(A)"
  and prem1: "l = m @ [b] ==> R"
  and prem2: "[| initseg(A, l, m); b: A |] ==> R"
  shows "R"
apply (insert prem)
apply (rule major [THEN initseg_right_appE])
apply assumption
apply (rule prem2)
apply assumption
apply (erule ConsE)
apply assumption
apply (case_tac "initseg(A, l, m)")
apply (rule prem2)
apply assumption
apply (erule ConsE)
apply assumption
apply (rule prem1)
apply hypsubst
apply (erule_tac a="x" in list.cases)
apply hypsubst
apply (erule notE)
apply simp_all
done

(** We can regard a list as a poset under initseg **)
lemma poset_initseg:
    "poset(initseg(A), list(A))"
apply (rule posetI)
apply (erule initseg_refl)
apply (erule initseg_antisym, assumption)
apply (erule initseg_trans, assumption)
done

lemma initseg_downset_forms_a_chain:
  "l: list(A) ==> chain(initseg(A), downset(initseg(A), list(A), l))"
apply (rule chainI)
apply (rule poset_initseg [THEN downset_subset [THEN poset_subset]])
apply (blast elim!: downsetE initsegE app_appE intro!: initseg_appI1)
done

lemma initseg_appI3:
  "[| initseg(A, y, z); x: list(A) |] ==> initseg(A, y, z@x)"
apply (unfold initseg_def)
apply (elim conjE bexE)
apply (assumption | rule conjI app_type)+
apply (rule bexI)
apply hypsubst
apply (drule app_typeD, assumption)
apply (simp add: app_assoc)
apply (assumption | rule app_type)+
done

lemma initseg_downset_is_Finite:
  "l: list(A) ==> Finite(downset(initseg(A), list(A), l))"
apply (erule list_append_induct)
apply (rule_tac P="%x. Finite(x)" in ssubst)
apply (rule_tac [2] Finite_cons)
apply (rule_tac [2] Finite_0)
apply (rule_tac [2] P="%x. Finite(x)" in ssubst)
apply (erule_tac [3] Finite_cons)
apply (rule_tac [2] equalityI)
apply (rule equalityI)
apply (safe elim!: downsetE initseg_NilE)
apply (rule refl)
apply (rule downsetI)
apply (rule_tac [4] downsetI)
apply (rule_tac [5] initseg_refl)
apply (rule_tac [6] downsetI)
apply (erule_tac [7] initseg_appI3)
apply (assumption | rule list.intros initseg_NilI)+
defer 1
apply (assumption | rule list.intros app_type)+
apply (erule initseg_right_appE)
apply assumption
apply (erule notE)
apply (rule downsetI)
apply assumption+
apply (rename_tac u v)
apply (erule_tac a="u" in list.cases)
apply simp_all
apply (erule notE)
apply (assumption | rule downsetI initseg_refl)+
done

end
