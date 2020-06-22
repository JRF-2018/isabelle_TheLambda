(*
    File:        NthNBQuant.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open Nth;

qed_goal "mem_nat_in_nat" Nat.thy
    "[| a: b; b: nat |] ==> a: nat"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac lt_nat_in_nat 1),
     (etac ltI 1),
     (etac nat_into_Ord 1),
     (atac 1)]);

qed_goal "UN_succ" ZF.thy
    "(UN z: succ(n). f(z)) = (UN z: n. f(z)) Un f(n)"
  (fn _ =>
    [(rtac (Un_commute RSN (2, trans)) 1),
     (simp_tac ZF_ss 1)]);

qed_goalw "nth_0" Nth.thy [nth_def]
    "nth(Cons(a,l), 0) = a"
  (fn _ =>
    [(res_inst_tac [("P", "%x. hd(x) = a")] (drop_0 RS ssubst) 1),
     (rtac hd_Cons 1)]);

qed_goalw "nth_Cons_succ" Nth.thy [nth_def]
    "n: nat ==> nth(Cons(a,l), succ(n)) = nth(l, n)"
  (fn [prem] =>
    [(res_inst_tac [("P", "%x. hd(x) = ?X")] 
    (prem RS drop_succ_Cons RS ssubst) 1),
     (rtac refl 1)]);

qed_goalw "nth_Nil" Nth.thy [nth_def, hd_def]
    "n: nat ==> nth(Nil, n) = 0"
  (fn [prem] =>
    [(rtac (prem RS drop_Nil RS ssubst) 1),
     (resolve_tac list.case_eqns 1)]);

qed_goalw "nth_type" Nth.thy [nth_def, hd_def]
    "[| n: nat; l: list(A) |] ==> nth(l, n): A Un {0}"
  (fn prems =>
    [(rtac (prems MRS drop_type RS list.elim) 1),
     (etac ssubst 1),
     (etac ssubst 2),
     (rtac UnI2 1),
     (rtac UnI1 2),
     (resolve_tac (list.case_eqns RL [ssubst]) 1),
     (rtac singletonI 1),
     (eresolve_tac (list.case_eqns RL [ssubst]) 1)]);

qed_goal "nth_over_length_lemma" Nth.thy
    "[| n: nat; l: list(A); length(l) le n |] ==> nth(l, n) = 0"
  (fn [n_nat, l_list, prem] =>
    [(rtac (prem RS rev_mp) 1),
     (rtac (n_nat RSN (2, bspec)) 1),
     (list_ind_tac "l" [l_list] 1),
     (ALLGOALS (rtac ballI)),
     (rtac impI 1),
     (etac nth_Nil 1),
     (etac nat_induct 1),
     (ALLGOALS (rtac impI)),
     (asm_full_simp_tac list_ss 1),
     (etac FalseE 1),
     (asm_full_simp_tac (list_ss addsimps [nth_Cons_succ]) 1)]);

fun nth_ss_solver typechecks prems = (eresolve_tac [FalseE]) ORELSE'
    (type_auto_tac typechecks prems) ORELSE'
    (resolve_tac [notFalseI]);

val nthlemmas_ss = list_ss delsimps Collect_simps delsimps arith_typechecks
    addsimps nbquant_simps
    addcongs nbquant_congs
    addsimps [nth_Cons_succ, nth_0, nth_Nil, UN_succ, UN_0, UN_constant,
	      Un_assoc RS sym, lt_nat_in_nat]
    addsimps (map prove_fun ["(UN y: A. 0) = 0",
			     "Collect(0, ?P) = 0", 
			     "{x: ?A . False} = 0",
			     "{x: ?A . True} = ?A"])
    setsolver (nth_ss_solver (arith_typechecks @ list_typechecks));

val nthlemmas_ss2 = use_nbquant_succ2 nthlemmas_ss;

qed_goal "nth_type2" Nth.thy
    "[| l: list(A); n < length(l) |] ==> nth(l, n): A"
  (fn [major, prem] =>
    [(rtac (prem RS rev_nbspec) 1),
     (list_ind_tac "l" [major] 1),
     (ALLGOALS (asm_simp_tac nthlemmas_ss2))]);

qed_goal "nth_app_right" Nth.thy
    "[| l: list(A); x < length(l) |] ==> nth(l@m, x) = nth(l, x)"
  (fn [major, prem] =>
    [(rtac (prem RS rev_nbspec) 1),
     (list_ind_tac "l" [major] 1),
     (ALLGOALS (asm_simp_tac nthlemmas_ss2))]);

qed_goal "nth_app_left" Nth.thy
    "l: list(A) ==> nth(l @ Cons(x, m), length(l)) = x"
  (fn [major] =>
    [(list_ind_tac "l" [major] 1),
     (ALLGOALS (asm_simp_tac nthlemmas_ss2))]);

qed_goal "nth_app_left2" Nth.thy
    "[| l: list(A); n: nat; length(l) le n |] ==> \
\              nth(l@m, n) = nth(m, n #- length(l))"
  (fn [major, n_nat, prem] =>
    [(rtac (prem RS rev_mp) 1),
     (rtac (n_nat RSN (2, bspec)) 1),
     (list_ind_tac "l" [major] 1),
     (ALLGOALS (asm_simp_tac nthlemmas_ss2)),
     (rtac ballI 1),
     (etac natE 1),
     (fast_tac (lt_cs addIs [length_type]) 1),
     (ALLGOALS (asm_simp_tac nthlemmas_ss2))]);

qed_goal "nth_existence_lemma" Nth.thy
    "[| ALL z < n :nat. f(z): A |] ==> \
\       EX l: list(A). length(l) = n & (ALL z < n :nat. nth(l, z) = f(z))"
  (fn [major] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (major RS nballD1 RS nat_induct) 1),
     (ALLGOALS (asm_full_simp_tac nthlemmas_ss)),
     (res_inst_tac [("x", "[]")] bexI 1),
     (rtac length_Nil 1),
     (safe_tac (nbquant_cs addSIs list.intrs)),
     (res_inst_tac [("x", "xa @ [f(length(xa))]")] bexI 1),
     (ALLGOALS (asm_simp_tac (nthlemmas_ss addsimps 
			      [nth_app_left2, length_app, nth_app_right,
			       add_0_right, add_succ_right,
			       diff_self_eq_0])))]);

qed_goal "nth_convert_list_type" Nth.thy
    "[| l: list(B); ALL z < length(l) :nat. nth(l, z): A |] ==> l: list(A)"
  (fn [l_list, prem] =>
    [(rtac (prem RS rev_mp) 1),
     (list_ind_tac "l" [l_list] 1),
     (ALLGOALS (asm_simp_tac nthlemmas_ss2)),
     (fast_tac (ZF_cs addSIs list.intrs) 1)]);

qed_goal "nth_map" Nth.thy
    "[| l: list(A); n < length(l) |] ==> nth(map(f, l), n) = f(nth(l, n))"
  (fn [l_list, n_len] =>
    [(rtac (n_len RS rev_nbspec) 1),
     (list_ind_tac "l" [l_list] 1),
     (ALLGOALS (asm_simp_tac nthlemmas_ss2))]);

qed_goal "nth_inj" Nth.thy
    "[| ALL z < length(l) :nat. nth(m, z) = nth(l, z); length(m) = length(l); \
\       l: list(A); m: list(B) |] ==> m = l"
  (fn [major, prem, l_list, m_list] =>
    [(rtac (prem RS rev_mp) 1),
     (rtac (major RS rev_mp) 1),
     (rtac (m_list RS rev_bspec) 1),
     (list_ind_tac "l" [l_list] 1),
     (ALLGOALS (asm_simp_tac nthlemmas_ss2)),
     (ALLGOALS (rtac (impI RS ballI))),
     (eres_inst_tac [("a", "x")] list.elim 2),
     (etac list.elim 1),
     (safe_tac nbquant_cs),
     (ALLGOALS (asm_full_simp_tac (nthlemmas_ss2 addsimps [Cons_iff]))),
     (etac (bspec RS mp RS mp) 1),
     (safe_tac ZF_cs)]);

(** mapnth **)
qed_goalw "mapnth_Nil" Nth.thy [mapnth_def]
    "mapnth(f, []) = []"
  (fn _ =>
    [(simp_tac list_ss 1)]);

qed_goal "mapnth_lemma" Nth.thy
    "n: nat ==> \
\       Cons(f(0, a), rec(n, [], %x r. r @ [f(succ(x), nth(l, x))])) = \
\          rec(n, [], %x r. r @ [f(x, nth(Cons(a, l), x))])@ \
\                      [f(n, nth(Cons(a, l), n))]"
  (fn [prem] =>
    [(nat_ind_tac "n" [prem] 1),
     (asm_simp_tac nthlemmas_ss 1),
     (asm_full_simp_tac (nthlemmas_ss delsimps [app_Cons]
		       addsimps [app_Cons RS sym]) 1)]);

qed_goalw "mapnth_Cons" Nth.thy [mapnth_def]
    "[| l: list(A) |] ==> \
\        mapnth(f, Cons(a, l)) = Cons(f(0, a), mapnth(%x. f(succ(x)), l))"
  (fn [prem] =>
    [(rtac (mapnth_lemma RS sym RSN (2, trans)) 1),
     (simp_tac list_ss 1),
     (rtac (prem RS length_type) 1)]);

qed_goalw "mapnth_Cons2" Nth.thy [mapnth_def]
    "[| length(l): nat |] ==> \
\        mapnth(f, Cons(a, l)) = Cons(f(0, a), mapnth(%x. f(succ(x)), l))"
  (fn [prem] =>
    [(rtac (mapnth_lemma RS sym RSN (2, trans)) 1),
     (simp_tac list_ss 1),
     (rtac prem 1)]);

qed_goal "rec_nth_app_right" Nth.thy
    "[| n: nat; l: list(A) |] ==> n le length(l) --> \
\        rec(n, [], %n r. r @ [f(n, nth(l@m, n))]) = \
\        rec(n, [], %n r. r @ [f(n, nth(l, n))])"
  (fn [prem1, prem2] =>
    [(cut_facts_tac [prem2] 1),
     (nat_ind_tac "n" [prem1] 1),
     (rtac impI 2),
     (rotate_tac 3 2),
     (ALLGOALS (asm_full_simp_tac (nthlemmas_ss addsimps 
				   [leI, nth_app_right])))]);

qed_goalw "mapnth_type" Nth.thy [mapnth_def]
    "[| l: list(A); !! n x. [| n: nat; x: A |] ==> f(n, x): B |] \
\           ==> mapnth(f, l): list(B)"
  (fn [prem1, prem2] =>
    [(rtac (prem1 RS list_append_induct) 1),
     (simp_tac list_ss 1),
     (asm_simp_tac (nthlemmas_ss addsimps [length_app, add_succ_right, 
				   rec_nth_app_right RS mp,
				   add_0_right]) 1),
     (etac app_type 1),
     (resolve_tac list.intrs 1),
     (rtac prem2 1),
     (rtac nth_type2 2),
     (REPEAT (CHANGED (asm_simp_tac (nthlemmas_ss addsimps 
				   [length_app, add_succ_right, 
				   add_0_right]) 1)))]);

qed_goalw "mapnth_app_last" Nth.thy [mapnth_def]
    "l: list(A) ==> \
\         mapnth(f, l@[a]) = mapnth(f, l) @ [f(length(l), a)]"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_simp_tac (nthlemmas_ss addsimps
		       [length_app, add_succ_right, add_0_right,
			rec_nth_app_right RS mp,
			diff_self_eq_0,
			nth_app_left2]) 1)]);

qed_goal "mapnth_type2" Nth.thy
    "l: list(A) ==> mapnth(f, l): list({f(n, x). <n,x>: nat*A})"
  (fn [prem] =>
    [(rtac (prem RS mapnth_type) 1),
     (res_inst_tac [("P", "%x. x: ?X"), ("b", "f(n, x)"), 
		  ("a", "split(f, <n, x>)")] ssubst 1),
     (simp_tac ZF_ss 1),
     (rtac RepFunI 1),
     (etac SigmaI 1),
     (atac 1)]);

qed_goal "length_mapnth" Nth.thy
    "l: list(A) ==> length(mapnth(f, l)) = length(l)"
  (fn [prem] =>
    [(rtac (prem RS list_append_induct) 1),
     (simp_tac (list_ss addsimps [mapnth_Nil]) 1),
     (forw_inst_tac [("f", "f")] mapnth_type2 1),
     (asm_simp_tac (list_ss addsimps [mapnth_app_last, length_app,
				    add_succ_right, add_0_right]) 1)]);

qed_goal "nth_mapnth" Nth.thy
    "[| l: list(A); n < length(l) |] ==> \
\               nth(mapnth(f, l), n) = f(n, nth(l, n))"
  (fn [prem1, prem2] =>
    [(rtac (prem2 RS rev_nbspec) 1),
     (rtac (prem1 RS list_append_induct) 1),
     (ALLGOALS (asm_simp_tac (nthlemmas_ss addsimps 
			      [length_app, add_succ_right, add_0_right,
			       mapnth_app_last]))),
     (forw_inst_tac [("f", "f")] mapnth_type2 1),
     (forw_inst_tac [("f1", "f")] (length_mapnth RS sym) 1),
     (safe_tac nbquant_cs),
     (etac length_type 1),
     (rotate_tac 3 1),
     (ALLGOALS (asm_full_simp_tac 
		(nthlemmas_ss addsimps [nth_app_left, nth_app_right,
					nth_app_left2, diff_self_eq_0]))),
     (etac nbspec 1),
     (atac 1)]);

qed_goal "map_mapnth" Nth.thy
    "l: list(A) ==> map(f, mapnth(g, l)) = mapnth(%x r. f(g(x, r)), l)"
  (fn [prem1] =>
    [(cut_facts_tac [prem1] 1),
     (subgoals_tac ["mapnth(g, l): list(?B)"] 1),
     (rtac nth_inj 1),
     (REPEAT (ares_tac [map_type2, mapnth_type2] 3)),
     (ALLGOALS (asm_simp_tac (nthlemmas_ss 
			      addsimps [length_map, length_mapnth,
					nth_map, nth_mapnth])))]);

qed_goal "mapnth_map" Nth.thy
    "l: list(A) ==> mapnth(f, map(g, l)) = mapnth(%x r. f(x, g(r)), l)"
  (fn [prem1] =>
    [(cut_facts_tac [prem1] 1),
     (subgoals_tac ["map(g, l): list(?B)"] 1),
     (rtac nth_inj 1),
     (REPEAT (ares_tac [map_type2, mapnth_type2] 3)),
     (ALLGOALS (asm_simp_tac (nthlemmas_ss addsimps 
			      [length_map, length_mapnth,
			       nth_map, nth_mapnth])))]);

qed_goal "mapnth_mapnth" Nth.thy
    "l: list(A) ==> mapnth(f, mapnth(g, l)) = mapnth(%x r. f(x, g(x, r)), l)"
  (fn [prem1] =>
    [(cut_facts_tac [prem1] 1),
     (subgoals_tac ["mapnth(g, l): list(?B)"] 1),
     (rtac nth_inj 1),
     (REPEAT (ares_tac [map_type2, mapnth_type2] 3)),
     (ALLGOALS (asm_simp_tac (nthlemmas_ss addsimps 
			      [length_mapnth, nth_mapnth])))]);

(** nth_0E **)
qed_goal "nth_0E_lemma" Nth.thy
    "l: list(A) ==> ALL a. 0 < length(l) --> nth(l, 0) = a --> \
\                                (EX m: list(A). a: A & l = Cons(a, m))"
  (fn [major] =>
    [(rtac (major RS list.elim) 1),
     (asm_simp_tac (IFOL_ss addsimps [length_Nil]) 1),
     (fast_tac lt_cs 1),
     (asm_simp_tac nthlemmas_ss 1),
     (REPEAT (resolve_tac [impI, allI] 1)),
     (rtac bexI 1),
     (REPEAT (hyp_subst_tac 1)),
     (REPEAT (ares_tac [refl, Cons_iff RS iffD2, conjI] 1))]);

qed_goal "nth_0E" Nth.thy
    "[| nth(l, 0) = a; \
\       !!m. [| a: A; m: list(A); l = Cons(a, m) |] ==> P; \
\       l: list(A); 0 < length(l) |] ==> P"
  (fn [major, prem, l_list, l_len] =>
    [(rtac (l_list RS nth_0E_lemma RS spec RS mp RS mp RS bexE) 1),
     (etac conjE 3),
     (rtac prem 3),
     (REPEAT (ares_tac [major, l_len] 1))]);

qed_goal "length_0E" Nth.thy
    "[| length(l) = 0;  l = [] ==> P; l: list(A) |] ==> P"
  (fn [major, prem, l_list] =>
    [(rtac (l_list RS list.elim) 1),
     (etac prem 1),
     (cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps [length_Cons]) 1),
     (etac succ_neq_0 1)]);

val nth_typechecks = arith_typechecks @ list_typechecks @ 
    [nth_type2, mapnth_type2, mapnth_type];

val nth_simps = [nth_Cons_succ, nth_0, nth_Nil,
		 mapnth_Nil, mapnth_Cons2];

val nth_ss = nthlemmas_ss
    addsimps [mapnth_Nil, mapnth_Cons2]
    addsimps [Cons_iff, add_0_right, add_succ_right, length_app,
	      app_right_Nil, nth_app_right, nth_app_left]
    setsolver (nth_ss_solver nth_typechecks);
