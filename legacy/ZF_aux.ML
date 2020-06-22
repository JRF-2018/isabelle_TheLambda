(*
    File:        ZF_aux.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

qed_goal "function_apply_eq" FOL.thy
    "a = b ==> f(a) = f(b)"
  (fn [prem] =>
    [(rtac (prem RS subst) 1),
     (rtac refl 1)]);

qed_goal "singleton_iff2" ZF.thy
    "{A} = {B} <-> A = B"
  (fn prems =>
    [(rtac iffI 1),
     (fast_tac ZF_cs 2),
     (etac equalityE 1),
     (dtac singleton_subsetD 1),
     (fast_tac ZF_cs 1)]);

val Pow_Un_0_simps = map prove_fun ["Pow(A) Un {0} = Pow(A)",
				    "{0} Un Pow(A) = Pow(A)"];

val succ_neq_self_simps = [succ_neq_self, succ_neq_self RS not_sym];

(** disjoint **)
qed_goal "disjointI" ZF.thy
    "[| !!x. [| x: X; x: Y |] ==> False |] ==> X Int Y = 0"
  (fn [major] =>
    [(safe_tac eq_cs),
     (rtac FalseE 1),
     (REPEAT (ares_tac [major] 1))]);

qed_goal "disjointE" ZF.thy
    "[| A Int B = 0; x: A; x: B |] ==> R"
  (fn major::prems =>
    [(cut_facts_tac [prems MRS IntI] 1),
     (dtac (major RS subst) 1),
     (etac emptyE 1)]);

qed_goal "disjoint_sym" ZF.thy
    "A Int B = 0 ==> B Int A = 0"
  (fn [major] =>
    [(rtac (Int_commute RS trans) 1),
     (rtac major 1)]);

qed_goal "disjoint_subset" ZF.thy
    "[| A Int B = 0; C <= A; D <= B |] ==> C Int D = 0"
  (fn [major, prem1, prem2] =>
    [(rtac disjointI 1),
     (rtac (major RS disjointE) 1),
     (etac (prem1 RS subsetD) 1),
     (etac (prem2 RS subsetD) 1)]);

qed_goal "disjoint_UnI" ZF.thy
    "[| A Int C = 0; B Int C = 0 |] ==> (A Un B) Int C = 0"
  (fn [prem1, prem2] =>
    [(rtac disjointI 1),
     (etac UnE 1),
     (etac (prem2 RS disjointE) 2),
     (etac (prem1 RS disjointE) 1),
     (REPEAT (atac 1))]);

qed_goal "disjoint_Un_iff" ZF.thy
    "(A Un B) Int C = 0 <-> A Int C = 0 & B Int C = 0"
  (fn _ =>
    [(rtac iffI 1),
     (rtac disjoint_UnI 2),
     (rtac conjI 1),
     (etac disjoint_subset 2),
     (etac disjoint_subset 1),
     (safe_tac ZF_cs)]);

qed_goal "disjoint_Un_iff2" ZF.thy
    "A Int (B Un C) = 0 <-> A Int B = 0 & A Int C = 0"
  (fn _ =>
    [(rtac iffI 1),
     (rtac (disjoint_UnI RS disjoint_sym) 2),
     (rtac conjI 1),
     (etac disjoint_subset 2),
     (etac disjoint_subset 1),
     (safe_tac ZF_cs),
     (REPEAT (etac disjoint_sym 1))]);

qed_goal "disjoint_cons_iff" ZF.thy
    "cons(a, A) Int B = 0 <-> a ~: B & A Int B = 0"
  (fn _ =>
    [(fast_tac (ZF_cs addSIs [disjointI] addEs [disjointE]) 1)]);

qed_goal "disjoint_cons_iff2" ZF.thy
    "A Int cons(b, B) = 0 <-> A Int B = 0 & b ~: A"
  (fn _ =>
    [(fast_tac (ZF_cs addSIs [disjointI] addEs [disjointE]) 1)]);

(** continuous **)
qed_goal "domain_continuous" ZF.thy
    "domain(Union(X)) = (UN x: X. domain(x))"
  (fn _ =>
    [(fast_tac eq_cs 1)]);

val continuous_simps = [domain_continuous] @ map prove_fun 
    ["{f(x). x: {g(y). y: X}} = {f(g(y)). y: X}",
     "Union(X) * A = (UN x: X. x * A)"];


(** Nat **)
qed_goal "mem_nat_in_nat" Nat.thy
    "[| a: b; b: nat |] ==> a: nat"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac lt_nat_in_nat 1),
     (etac ltI 1),
     (etac nat_into_Ord 1),
     (atac 1)]);

qed_goal "lt_Un_eq_lemma" Nat.thy
    "A < B ==> A Un B = B"
  (fn [prem] =>
    [(cut_facts_tac [prem RS leI RS le_imp_subset] 1),
     (fast_tac eq_cs 1)]);


qed_goal "le_Un_eq_lemma" Nat.thy
    "A le B ==> A Un B = B"
  (fn [prem] =>
    [(cut_facts_tac [prem RS le_imp_subset] 1),
     (fast_tac eq_cs 1)]);

qed_goal "nat_succ_Un" Nat.thy
    "[| A: nat; B: nat |] ==> succ(A) Un succ(B) = succ(A Un B)"
  (fn prems =>
    [(rtac (prems RL [nat_into_Ord] MRS Ord_linear_lt) 1),
     (hyp_subst_tac 2),
     (fast_tac eq_cs 2),
     (rtac (lt_Un_eq_lemma RS ssubst) 1),
     (atac 1),
     (dtac succ_leI 1),
     (etac (lt_Un_eq_lemma RS ssubst) 1),
     (rtac refl 1),
     (rtac (lt_Un_eq_lemma RS (Un_commute RS trans) RS ssubst) 1),
     (atac 1),
     (dtac succ_leI 1),
     (etac (lt_Un_eq_lemma RS (Un_commute RS trans) RS ssubst) 1),
     (rtac refl 1)]);

qed_goal "nat_UnI" Nat.thy
    "[| A: nat; B: nat |] ==> A Un B: nat"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac (prems RL [nat_into_Ord] MRS Ord_linear_lt) 1),
     (TRYALL (dtac lt_Un_eq_lemma)),
     (rtac (Un_commute RS subst) 3),
     (ALLGOALS (asm_simp_tac (IFOL_ss addsimps [Un_absorb])))]);

val gt_not_eq = prove_goal Nat.thy
    "!!m.[| p < n; n:nat|]==> n~=p"
  (fn _ =>
    [(fast_tac lt_cs 1)]);

val lt_asym_if = prove_goal Nat.thy
    "!!m. p < n ==> if (n < p, a, b) = b"
  (fn _ =>
    [(fast_tac (lt_cs addEs [lt_asym] addIs [if_not_P]) 1)]);

val le_asym_if = prove_goal Nat.thy
    "!!m. p le n ==> if (n < p, a, b) = b"
  (fn _ =>
    [(fast_tac (lt_cs addEs [lt_asym] addIs [if_not_P]) 1)]);

val lt_irrefl_if = prove_goal Nat.thy
    "if (n < n, a, b) = b"
  (fn _ =>
    [(fast_tac (lt_cs addIs [if_not_P]) 1)]);

(** Arith **)
val succ_pred = prove_goal Arith.thy 
    "!!i.[|j:nat; i:nat|]==> i < j --> succ(j #- 1) = j"
 (fn prems =>[(etac nat_induct 1),
	      (fast_tac lt_cs 1),
	      (asm_simp_tac arith_ss 1)]);

val lt_pred = prove_goal Arith.thy
    "!!i.[|succ(x)<n; n:nat; x:nat|]==> x < n#-1 "
  (fn prems =>
    [(resolve_tac [succ_leE] 1),
     (forward_tac [nat_into_Ord RS le_refl RS lt_trans] 1 THEN assume_tac 1),
     (asm_simp_tac (arith_ss addsimps [succ_pred]) 1)]);

val gt_pred = prove_goal Arith.thy
    "!!i.[|n < succ(x); p<n; p:nat; n:nat; x:nat|]==> n#-1 < x "
  (fn prems =>
    [(resolve_tac [succ_leE] 1),
     (asm_simp_tac (arith_ss addsimps [succ_pred]) 1)]);

qed_goal "lt_imp_le_pred" Arith.thy
    "[| i < j; j: nat |] ==> i le j #- 1"
  (fn [major, prem] =>
    [(rtac (prem RS natE) 1),
     (ALLGOALS (cut_facts_tac [major])),
     (ALLGOALS (asm_full_simp_tac arith_ss))]);

qed_goal "diff_eq_0D" Arith.thy
    "[| m #- n = 0; m: nat; n: nat |] ==> m le n"
  (fn [major, sub, prem] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (sub RSN (2, bspec)) 1),
     (nat_ind_tac "n" [prem] 1),
     (rtac ballI 2),
     (eres_inst_tac [("n", "x")] natE 2),
     (ALLGOALS (asm_simp_tac arith_ss))]);

qed_goal "Un_diff" Arith.thy
    "[| m: nat; n: nat; l: nat |] ==> (m Un n) #- l = (m #- l) Un (n #- l)"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem2 RSN (2, bspec)) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (nat_ind_tac "m" [prem1] 1),
     (REPEAT (rtac ballI 2)),
     (eres_inst_tac [("n", "x")] natE 2),
     (eres_inst_tac [("n", "xa")] natE 3),
     (TRYALL (REPEAT o hyp_subst_tac)),
     (forw_inst_tac [("A", "m1"), ("B", "xc")] nat_UnI 4),
     (ALLGOALS (asm_simp_tac (arith_ss addsimps [nat_succ_Un])))]);

qed_goal "Un_least_ltE" Ordinal.thy
    "[| i Un j < k; Ord(i); Ord(j); \
\       [| i < k; j < k |] ==> R |] ==> R"
  (fn [major, prem1, prem2, prem3] =>
    [(cut_facts_tac [[prem1, prem2, major] MRS (Un_least_lt_iff RS iffD1)] 1),
     (etac conjE 1),
     (REPEAT (ares_tac [prem3] 1))]);

qed_goal "Un_least_lt_iff" Ordinal.thy
    "[| Ord(i); Ord(j) |] ==> i Un j < k <-> i < k & j < k"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (fast_tac (lt_cs addSEs [Un_least_ltE] addIs [Un_least_lt]) 1)]);

qed_goal "diff_le_mono1" Arith.thy
    "[| i le j; i: nat; j: nat; k: nat |] ==> i #- k le j #- k"
  (fn [major, prem1, prem2, prem3] =>
    [(rtac (major RS rev_mp) 1),
     (rtac (prem2 RSN (2, bspec)) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (nat_ind_tac "i" [prem1] 1),
     (rtac ballI 2),
     (eres_inst_tac [("n", "x")] natE 2),
     (hyp_subst_tac 3),
     (rtac ballI 3),
     (eres_inst_tac [("n", "xb")] natE 3),
     (hyp_subst_tac 4),
     (ALLGOALS (asm_simp_tac arith_ss))]);

qed_goal "diff_ltD" Arith.thy
    "[| i #- j < k; i: nat; j: nat; k: nat |] ==> i < j #+ k"
  (fn [major, prem1, prem2, prem3] =>
    [(cut_facts_tac [prem3] 1),
     (rtac (major RS rev_mp) 1),
     (rtac (prem1 RSN (2, bspec)) 1),
     (nat_ind_tac "j" [prem2] 1),
     (rtac (impI RS ballI) 2),
     (eres_inst_tac [("n", "x")] natE 2),
     (hyp_subst_tac 3),
     (rotate_tac 4 3),
     (ALLGOALS (asm_full_simp_tac arith_ss))]);

qed_goal "diff_leI" Arith.thy
    "[| i le j #+ k; i: nat; j: nat; k: nat |] ==> i #- j le k"
  (fn [major, prem1, prem2, prem3] =>
    [(cut_facts_tac [prem3] 1),
     (rtac (major RS rev_mp) 1),
     (rtac (prem1 RSN (2, bspec)) 1),
     (nat_ind_tac "j" [prem2] 1),
     (rtac (impI RS ballI) 2),
     (eres_inst_tac [("n", "x")] natE 2),
     (TRYALL hyp_subst_tac),
     (rotate_tac 4 3),
     (ALLGOALS (asm_full_simp_tac arith_ss))]);

qed_goal "diff_le_iff" Arith.thy
    "[| i: nat; j: nat; k: nat |] ==> i #- j le k <-> i le j #+ k"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (rtac iffI 1),
     (rtac diff_leI 2),
     (dtac diff_ltD 1),
     (asm_full_simp_tac (arith_ss addsimps [add_succ_right]) 4),
     (REPEAT (ares_tac [nat_succI] 1))]);

qed_goal "lt_diffI" Arith.thy
    "[| i #+ j < k; i: nat; j: nat; k: nat |] ==> j < k #- i"
  (fn [major, prem1, prem2, prem3] =>
    [(cut_facts_tac [prem2] 1),
     (rtac (major RS rev_mp) 1),
     (rtac (prem1 RSN (2, bspec)) 1),
     (nat_ind_tac "k" [prem3] 1),
     (rtac (impI RS ballI) 2),
     (eres_inst_tac [("n", "x")] natE 2),
     (TRYALL hyp_subst_tac),
     (rotate_tac 4 3),
     (ALLGOALS (asm_full_simp_tac arith_ss))]);

qed_goal "lt_diffD" Arith.thy
    "[| j < k #- i; i: nat; j: nat; k: nat |] ==> i #+ j < k"
  (fn [major, prem1, prem2, prem3] =>
    [(cut_facts_tac [prem2] 1),
     (rtac (major RS rev_mp) 1),
     (rtac (prem1 RSN (2, bspec)) 1),
     (nat_ind_tac "k" [prem3] 1),
     (rtac (impI RS ballI) 2),
     (eres_inst_tac [("n", "x")] natE 2),
     (TRYALL hyp_subst_tac),
     (rotate_tac 4 3),
     (ALLGOALS (asm_full_simp_tac arith_ss))]);

qed_goal "lt_diff_iff" Arith.thy
    "[| i: nat; j: nat; k: nat |] ==> j < k #- i <-> i #+ j < k"
  (fn prems =>
    [(rtac iffI 1),
     (etac lt_diffI 2),
     (etac lt_diffD 1),
     (REPEAT (ares_tac prems 1))]);

qed_goal "diff_diff_eq_diff_add" Arith.thy
    "[| i: nat; j: nat; k: nat |] ==> i #- j #- k = i #- (k #+ j)"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem1 RSN (2, bspec)) 1),
     (rtac (prem3 RSN (2, bspec)) 1),
     (nat_ind_tac "j" [prem2] 1),
     (rtac (ballI RS ballI) 2),
     (eres_inst_tac [("n", "xa")] natE 2),
     (ALLGOALS (asm_simp_tac (arith_ss addsimps 
			    [add_succ_right, add_0_right])))]);

(** Quantifiers Bounded by Natural Number **)

val nat_ltI = standard (nat_into_Ord RSN (2, ltI));

qed_goal "ball_mem_nat_in_nat" Nat.thy
    "!!n. n: nat ==> (ALL x:n. x:nat) <-> True"
  (fn prems =>
    [(fast_tac (ZF_cs addIs [mem_nat_in_nat]) 1)]);

qed_goal "nat_succ_mono" Nat.thy
    "!!n. [| n:m; m: nat |] ==> succ(n): succ(m)"
  (fn prems =>
    [(rtac ltD 1),
     (asm_simp_tac (nat_ss addsimps [nat_ltI]) 1)]);

qed_goal "nat_ball_succ" Nat.thy
    "!!n. n: nat ==> (ALL x:succ(n). P(x)) <-> P(0) & (ALL x:n. P(succ(x)))"
  (fn prems =>
    [(safe_tac ZF_cs),
     (TRYALL ((dtac nat_ltI) THEN' atac)),
     (etac natE 3),
     (etac natE 5),
     (REPEAT (fast_tac lt_cs 3)),
     (hyp_subst_tac 3),
     (rtac (lt_nat_in_nat RS natE) 3),
     (etac nat_succI 4),
     (atac 3),
     (hyp_subst_tac 4),
     (etac bspec 4),
     (rtac ltD 4),
     (asm_full_simp_tac (nat_ss addsimps [leI]) 4),
     (fast_tac ZF_cs 3),
     (ALLGOALS (etac bspec)),
     (ALLGOALS (rtac ltD)),
     (ALLGOALS (asm_full_simp_tac nat_ss))]);

qed_goal "nat_bex_succ" Nat.thy
    "!!n. n: nat ==> (EX x:succ(n). P(x)) <-> P(0) | (EX x:n. P(succ(x)))"
  (fn prems =>
    [(safe_tac ZF_cs),
     (TRYALL ((dtac nat_ltI) THEN' atac)),
     (etac natE 2),
     (etac natE 1),
     (REPEAT (fast_tac lt_cs 1)),
     (hyp_subst_tac 1),
     (rtac (lt_nat_in_nat RS natE) 1),
     (etac nat_succI 2),
     (atac 1),
     (hyp_subst_tac 2),
     ((swap_res_tac [bexI] 2) THEN (atac 2)),
     (rtac ltD 2),
     (asm_full_simp_tac (nat_ss addsimps [leI]) 2),
     (fast_tac ZF_cs 1),
     (ALLGOALS (etac bexI)),
     (ALLGOALS (rtac ltD)),
     (ALLGOALS (asm_full_simp_tac nat_ss))]);

qed_goal "nat_ball_cong" Nat.thy
  "[| A = A'; !!x. x < A' ==> P(x) <-> P'(x); \
\     !!x. [| x: A'; A'~: nat |] ==> P(x) <-> P'(x) \
\  |]  ==> Ball(A, P) <-> Ball(A', P')"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem1 RS ball_cong) 1),
     (excluded_middle_tac "A': nat" 1),
     (rtac prem2 2),
     (etac prem3 1),
     (REPEAT (ares_tac [nat_ltI] 1))]);

qed_goal "nat_bex_cong" Nat.thy
  "[| A = A'; !!x. x < A' ==> P(x) <-> P'(x); \
\     !!x. [| x: A'; A'~: nat |] ==> P(x) <-> P'(x) \
\  |]  ==> Bex(A, P) <-> Bex(A', P')"
  (fn [prem1, prem2, prem3] =>
    [(rtac (prem1 RS bex_cong) 1),
     (excluded_middle_tac "A': nat" 1),
     (rtac prem2 2),
     (etac prem3 1),
     (REPEAT (ares_tac [nat_ltI] 1))]);

val nat_bquant_congs = [nat_ball_cong, nat_bex_cong];

val nat_bquant_succ1 = map prove_fun
 [ "(ALL x:succ(i).P(x)) <-> P(i) & (ALL x:i.P(x))",
   "(EX  x:succ(i).P(x)) <-> P(i) | (EX  x:i.P(x))" ];

val nat_bquant_succ2 = [nat_ball_succ, nat_bex_succ];

fun use_nat_bquant_succ2 ss = ss delsimps nat_bquant_succ1 
    addsimps nat_bquant_succ2;
