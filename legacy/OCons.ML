(*
    File:        OCons.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open OCons;

qed_goalw "OCons_eq" OCons.thy [OCons_def]
    "OCons(n, <l, T>) = <Cons(n, l), T>"
  (fn _ =>
    [(rtac theI2 1),
     (rtac ex1I 1),
     (REPEAT (ares_tac [exI, refl, conjI] 1)),
     (safe_tac (ZF_cs addSEs list.free_SEs))]);

qed_goalw "ODestr_eq" OCons.thy [ODestr_def]
    "ODestr(n, <Cons(n, l), T>) = <l, T>"
  (fn _ =>
    [(rtac theI2 1),
     (rtac ex1I 1),
     (REPEAT (ares_tac [exI, refl, conjI] 1)),
     (safe_tac (ZF_cs addSEs list.free_SEs))]);

qed_goalw "ODestr_empty1" OCons.thy [ODestr_def]
    "ODestr(n, <[], T>) = 0"
  (fn _ =>
    [(rtac the_0 1),
     (safe_tac (ZF_cs addSEs list.free_SEs))]);

qed_goalw "ODestr_empty2" OCons.thy [ODestr_def]
    "n ~= m ==> ODestr(n, <Cons(m, l), T>) = 0"
  (fn [prem] =>
    [(cut_facts_tac [prem] 1),
     (rtac the_0 1),
     (safe_tac (ZF_cs addSEs list.free_SEs))]);

qed_goal "lam_OCons_injective" OCons.thy
    "X <= list(A) * B ==> (lam u: X. OCons(n, u)): inj(X, Occ_shift(n, X))"
  (fn [prem] =>
    [(res_inst_tac [("d", "ODestr(n)")] lam_injective 1),
     (ALLGOALS (forward_tac [prem RS subsetD])),
     (safe_tac ZF_cs),
     (ALLGOALS (simp_tac (IFOL_ss addsimps [OCons_eq, ODestr_eq]))),
     (etac Occ_shiftI 1)]);

qed_goal "lam_ODestr_injective" OCons.thy
    "(lam u: Occ_shift(n, X). ODestr(n, u)): inj(Occ_shift(n, X), X)"
  (fn _ =>
    [(res_inst_tac [("d", "OCons(n)")] lam_injective 1),
     (safe_tac (ZF_cs addSEs [Occ_shiftE])),
     (ALLGOALS (simp_tac (IFOL_ss addsimps [OCons_eq, ODestr_eq])))]);

qed_goal "Occ_shift_cardinal" OCons.thy
    "X <= list(A) * B ==> |Occ_shift(n, X)| = |X|"
  (fn [prem] =>
    [(rtac cardinal_cong 1),
     (rtac eqpollI 1),
     (rewrite_goals_tac [lepoll_def]),
     (REPEAT (ares_tac [exI, prem RS lam_OCons_injective, 
                      lam_ODestr_injective] 1))]);
