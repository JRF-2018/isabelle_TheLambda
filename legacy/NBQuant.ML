(*
    File:        NBQuant.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open NBQuant;

(*** Universal quantifier bounded by a natural number ***)

qed_goalw "nballI" NBQuant.thy [NBall_def]
    "[| A: nat; !!x. x < A ==> P(x) |] ==> ALL x < A :nat. P(x)"
  (fn [major, prem] =>
    [(REPEAT (ares_tac [major, allI, prem, conjI, impI] 1))]);

qed_goalw "nballD1" NBQuant.thy [NBall_def]
    "ALL x < A :nat. P(x) ==> A: nat"
  (fn [major] =>
    [(rtac (major RS conjunct1) 1)]);

qed_goalw "nbspec" NBQuant.thy [NBall_def]
    "[| ALL x < A :nat. P(x); x < A |] ==> P(x)"
  (fn [major, prem] =>
    [(rtac (major RS conjunct2 RS spec RS mp) 1),
     (rtac prem 1)]);

qed_goalw "nballE" NBQuant.thy [NBall_def]
    "[| ALL x < A :nat. P(x);  [| A: nat;  P(x) |]==> Q; \
\      [| A: nat; ~ x < A |] ==> Q |] ==> Q"
  (fn major::prems =>
    [(cut_facts_tac [major RS conjunct1] 1),
     (rtac (major RS conjunct2 RS allE) 1),
     (etac impCE 1),
     (REPEAT ((eresolve_tac prems 1) THEN (atac 1)))]);

qed_goal "rev_nbspec" NBQuant.thy
    "!!x A P. [| x < A;  ALL x < A :nat. P(x) |] ==> P(x)"
  (fn _ =>
    [(REPEAT (ares_tac [nbspec] 1))]);

qed_goal "rev_nballE" NBQuant.thy
    "[| ALL x < A :nat. P(x);  [| A: nat; ~ x < A |] ==> Q;  \
\       [| A: nat; P(x) |] ==> Q |] ==> Q"
  (fn major::prems =>
    [(rtac (major RS nballE) 1),
     (REPEAT ((eresolve_tac prems 1) THEN (atac 1)))]);

qed_goal "nball_simp" NBQuant.thy 
    "!!A. A: nat ==> (ALL x < A :nat. True) <-> True"
 (fn _=> [ (REPEAT (ares_tac [TrueI,nballI,iffI] 1)) ]);

qed_goalw "nball_cong" NBQuant.thy [NBall_def]
    "[| A=A';  !!x. [| x: nat; A': nat; x < A' |] ==> P(x) <-> P'(x) |] \
\         ==> NBall(A,P) <-> NBall(A',P')"
  (fn prems =>
    [(safe_tac ZF_cs),
     (forward_tac [lt_nat_in_nat] 4),
     (forward_tac [lt_nat_in_nat] 2),
     (rotate_tac 2 3),
     (ALLGOALS (asm_full_simp_tac (FOL_ss addsimps prems))),
     (resolve_tac (prems RL [iffD1]) 1),
     (etac (spec RS mp) 4),
     (REPEAT (atac 1))]);

(*** Existential quantifier bounded by a natural number ***)

qed_goalw "nbexI" NBQuant.thy [NBex_def]
    "[| P(x);  x < A; A: nat |] ==> EX x < A :nat. P(x)"
 (fn prems=> [ (REPEAT (ares_tac (prems @ [exI,conjI]) 1)) ]);

(*Not of the general form for such rules; ~EX has become ALL~ *)
qed_goal "nbexCI" NBQuant.thy
    "[| ALL x < A :nat. ~P(x) ==> P(a);  a < A; A: nat |] \
\       ==> EX x < A :nat.P(x)"
  (fn prems =>
    [(rtac classical 1),
     (REPEAT (ares_tac (prems@[nbexI,nballI,notI,notE]) 1))]);

qed_goalw "nbexE" NBQuant.thy [NBex_def]
    "[| EX x < A:nat. P(x);  !!x. [| A: nat; x < A; P(x) |] ==> Q \
\    |] ==> Q"
  (fn major::prems =>
    [(rtac (major RS conjE) 1),
     (etac exE 1),
     (REPEAT (eresolve_tac (prems @ [asm_rl,conjE]) 1))]);

(*We do not even have (EX x:A. True) <-> True unless A is nonempty!!*)

qed_goalw "nbex_cong" NBQuant.thy [NBex_def]
    "[| A=A';  !!x. [| x: nat; A': nat; x < A' |] ==> P(x) <-> P'(x) \
\    |] ==> NBex(A,P) <-> NBex(A',P')"
  (fn prems =>
    [(simp_tac (FOL_ss addsimps prems addsimps [lt_nat_in_nat]
		addcongs [conj_cong]) 1)]);

val nbquant_cs = ZF_cs 
    addSIs [nballI, nat_into_Ord RS le_refl, succ_leI] 
    addIs [nbexI, nat_0I, nat_succI, leI] 
    addSEs [nbexE, lt_irrefl, lt0E, leI] addEs [rev_nballE]
    addSDs [succ_natD, le0D, succ_le_iff RS iffD1]
    addDs [nbspec];

qed_goal "nball_succ" NBQuant.thy
    "(ALL x < succ(a) :nat. P(x)) <-> P(0) & (ALL x < a :nat. P(succ(x)))"
  (fn _ =>
    [(excluded_middle_tac "a: nat" 1),
     (fast_tac nbquant_cs 1),
     (nat_ind_tac "a" [] 1),
     (fast_tac nbquant_cs 1),
     (safe_tac (nbquant_cs addSIs [nat_succI])),
     (etac swap 8),
     (eres_inst_tac [("n", "xb")] (lt_nat_in_nat RS natE) 5),
     (REPEAT (ares_tac [nat_succI] 5)),
     (hyp_subst_tac 5),
     (hyp_subst_tac 6),
     (TRYALL (DEPTH_SOLVE_1 o ((etac nbspec) THEN' (asm_simp_tac nat_ss)))),
     ((etac swap 2) THEN (etac nbspec 2)),
     (etac leI 2),
     ((etac swap 1) THEN (etac nbspec 1)),
     (etac leI 1),
     (res_inst_tac [("n", "x")] (lt_nat_in_nat RS natE) 1),
     (atac 1),
     (safe_tac (nbquant_cs addSIs [nat_succI])),
     (DEPTH_SOLVE ((etac nbspec 1)
		 THEN (asm_full_simp_tac nat_ss 1)))]);

qed_goal "nbex_succ" NBQuant.thy
    "a: nat ==> \
\      (EX x < succ(a) :nat. P(x)) <-> P(0) | (EX x < a :nat. P(succ(x)))"
  (fn [major] =>
    [(nat_ind_tac "a" [major] 1),
     (fast_tac nbquant_cs 1),
     (safe_tac (nbquant_cs addSIs [nat_succI])),
     (etac swap 5),
     (etac nbexI 2),
     (asm_simp_tac nat_ss 2),
     (forw_inst_tac [("m", "x")] lt_nat_in_nat 1),
     (eres_inst_tac [("n", "x")] natE 2),
     (TRYALL ((etac nbexI) THEN' (etac leI))),
     (safe_tac (nbquant_cs addSIs [nat_succI])),
     (asm_full_simp_tac nat_ss 1),
     ((swap_res_tac [nbexI] 1) THEN (atac 1) THEN (atac 1)),
     (etac nat_succI 1)]);

qed_goal "RepFun_cong_nat_lt" NBQuant.thy
    "[| A = B; !!x. [| x < B; B : nat |] ==> f(x) = g(x); \
\       !!x. [| x : B; B ~: nat |] ==> f(x) = g(x) \
\    |] ==> \
\         RepFun(A, f) = RepFun(B, g)"
  (fn [prem1, prem2, prem3] =>
    [(rtac RepFun_cong 1),
     (rtac prem1 1),
     (excluded_middle_tac "B: nat" 1),
     (etac prem3 1),
     (REPEAT (ares_tac [prem2, ltI, nat_into_Ord] 1))]);

qed_goal "Collect_cong_nat_lt" NBQuant.thy
    "[| A: nat; A = B; !!x. x < B ==> P(x) <-> Q(x) |] ==> \
\         Collect(A, P) = Collect(B, Q)"
  (fn [prem1, prem2, prem3] =>
    [(rtac Collect_cong 1),
     (REPEAT (ares_tac [prem2, prem3, ltI] 1)),
     (cut_facts_tac [prem1 RS nat_into_Ord] 1),
     (asm_full_simp_tac (IFOL_ss addsimps [prem2]) 1)]);

qed_goal "Replace_cong_nat_lt" NBQuant.thy
    "[| A: nat; A = B; !!x y. x < B ==> P(x, y) <-> Q(x, y) |] ==> \
\         Replace(A, P) = Replace(B, Q)"
  (fn [prem1, prem2, prem3] =>
    [(rtac Replace_cong 1),
     (REPEAT (ares_tac [prem2, prem3, ltI] 1)),
     (cut_facts_tac [prem1 RS nat_into_Ord] 1),
     (asm_full_simp_tac (IFOL_ss addsimps [prem2]) 1)]);

qed_goal "lam_cong_nat_lt" NBQuant.thy
    "[| A: nat; A = A'; !!x y. x < A' ==> b(x) = b'(x) |] ==> \
\         Lambda(A, b) = Lambda(A', b)"
  (fn [prem1, prem2, prem3] =>
    [(rtac lam_cong 1),
     (REPEAT (ares_tac [prem2, prem3, ltI] 1)),
     (cut_facts_tac [prem1 RS nat_into_Ord] 1),
     (asm_full_simp_tac (IFOL_ss addsimps [prem2]) 1)]);

val nat_ltI = standard (nat_into_Ord RSN (2, ltI));

val nbquant_simps = [nball_simp, nat_ltI] @ 
    (map (fn s => prove_goal NBQuant.thy s
	  (fn prems =>
	   [(cut_facts_tac prems 1),
	    (fast_tac (nbquant_cs addIs [equalityI] addSEs [leE]
		       addDs [lt_nat_in_nat]) 1)]))
     ["n: nat ==> (ALL x < n:nat. x:nat) <-> True",
      "(ALL x<0:nat. P(x)) <-> True",
      "(EX x<0:nat. P(x)) <-> False",
      "(ALL y<succ(x):nat. P(y)) <-> (ALL y<x:nat. P(y)) & P(x)",
      "x: nat ==> (EX y<succ(x):nat. P(y)) <-> (EX y<x:nat. P(y)) | P(x)"]);

val nbquant_congs = [nball_cong, nbex_cong];

val nbquant_succ1 = drop(4, nbquant_simps);
val nbquant_succ2 = [nball_succ, nbex_succ];

fun use_nbquant_succ2 ss = ss delsimps nbquant_succ1 addsimps nbquant_succ2;
