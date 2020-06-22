(*
    File:        OCons.thy
    Time-stamp:  <2020-06-22T03:54:20Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory OCons imports OccTools ZF.Cardinal begin

definition OCons :: "[i, i]=>i" where
"OCons(n, u) == THE v. EX l T. u = <l, T> & v = <Cons(n, l), T>"

definition ODestr :: "[i, i]=>i" where
"ODestr(n, u) == THE v. EX l T. v = <l, T> & u = <Cons(n, l), T>"


lemma OCons_eq:
  "OCons(n, <l, T>) = <Cons(n, l), T>"
apply (unfold OCons_def)
apply (rule theI2)
apply (rule ex1I)
apply (assumption | rule exI refl conjI)+
apply (safe elim!: list.free_elims)
done

lemma ODestr_eq:
  "ODestr(n, <Cons(n, l), T>) = <l, T>"
apply (unfold ODestr_def)
apply (rule theI2)
apply (rule ex1I)
apply (assumption | rule exI refl conjI)+
apply (safe elim!: list.free_elims)
done

lemma ODestr_empty1:
  "ODestr(n, <[], T>) = 0"
apply (unfold ODestr_def)
apply (rule the_0)
apply (safe elim!: list.free_elims)
done

lemma ODestr_empty2:
  "n ~= m ==> ODestr(n, <Cons(m, l), T>) = 0"
apply (unfold ODestr_def)
apply (rule the_0)
apply (safe elim!: list.free_elims)
done

lemma lam_OCons_injective:
  assumes prem: "X <= list(A) * B"
  shows "(lam u: X. OCons(n, u)): inj(X, Occ_shift(n, X))"
apply (rule_tac d="ODestr(n)" in lam_injective)
apply (frule_tac [2] prem [THEN subsetD])
apply (frule_tac [1] prem [THEN subsetD])
apply safe
apply (simp_all only: OCons_eq ODestr_eq)
apply (erule Occ_shiftI)
done

lemma lam_ODestr_injective:
  "(lam u: Occ_shift(n, X). ODestr(n, u)): inj(Occ_shift(n, X), X)"
apply (rule_tac d="OCons(n)" in lam_injective)
apply (safe elim!: Occ_shiftE)
apply (simp_all only: OCons_eq ODestr_eq)
done

lemma Occ_shift_cardinal:
  assumes prem: "X <= list(A) * B"
  shows "|Occ_shift(n, X)| = |X|"
apply (rule cardinal_cong)
apply (rule eqpollI)
apply (unfold lepoll_def)
apply (assumption | rule exI prem [THEN lam_OCons_injective]
         lam_ODestr_injective)+
done

end
