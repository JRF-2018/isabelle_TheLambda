(*
    File:        FNumber.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open FNumber;

local
    val con_defs = [TFZero_def, TFSucc_def];
    val con_iffs = con_defs RL [Ind_Syntax.def_swap_iff];
    structure Su = Standard_Sum;
    structure Pr = Standard_Prod;
    val free_SEs = Ind_Syntax.mk_free_SEs con_iffs @ Su.free_SEs
in
    structure FTag = 
	struct
	val con_defs = con_defs @ [FTag_def]
		
	val free_iffs = con_iffs @ 
	    [Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff, Pr.pair_iff];
	  
	val free_SEs = free_SEs;

	fun mk_free s =
	    prove_goalw FNumber.thy con_defs s
	    (fn prems => [cut_facts_tac prems 1, 
			  fast_tac (sum_cs addSEs free_SEs) 1]);

	val intrs = map mk_free ["TFZero: FTag",
				 "TFSucc: FTag"];
	exception Nth;
	fun nth(a::b, s) = if s = 0 then  a
                          else if s > 0 then nth(b, s - 1) else raise Nth
          | nth([], s) = raise Nth;

        val elim = prove_goalw FNumber.thy con_defs
            "[| T: FTag; \
\               !!x. [| T = TFZero |] ==> P; \
\               !!x. [| T = TFSucc |] ==> P \
\            |] ==> P"
            (fn major::prems =>
             [(cut_facts_tac [major] 1),
              (REPEAT (CHANGED (TRYALL (etac sumE)))),
              (ALLGOALS (fn i=>(rtac (nth(prems, i - 1)) i))),
              (ALLGOALS (fast_tac sum_cs))]);
        end
end;

fun FNum_ind_tac term prems i = 
    EVERY [res_inst_tac [("x",term)] FNum.induct i,
           ares_tac prems i];

val FNum_rec_eqns = map (fn s => prove_goal FNumber.thy s
                          (fn prems=>
                           [(rtac (FNum_rec_def RS def_Vrec RS trans) 1),
                            (simp_tac (rank_ss addsimps FNum.con_defs)  1)]))
    ["FNum_rec(FZero, case_Zero, case_Succ) = case_Zero",
     "FNum_rec(FSucc(M), case_Zero, case_Succ)\
\            = case_Succ(M, FNum_rec(M, case_Zero, case_Succ))"];

(*Type checking -- proved by induction, as usual*)
val FNum_rec_type = prove_goal FNumber.thy
    "[| M: FNum;    \
\       z: C(FZero);   \
\       !!M r. [| M: FNum;  r: C(M) |] ==> \
\                    h(M,r): C(FSucc(M))  \
\    |] ==> FNum_rec(M,z,h) : C(M)"
  (fn prems =>
    [(FNum_ind_tac "M" prems 1),
     (ALLGOALS (asm_simp_tac (ZF_ss addsimps
                 (prems@FNum_rec_eqns))))]);

val FTerm_cons_eqns = map (fn s =>
                           prove_goalw FNumber.thy 
                           ([FTerm_cons_def]@FTag.con_defs) s
                           (fn prems => [simp_tac nth_ss 1,
                                         simp_tac sum_ss 1]))
    ["FTerm_cons(TFZero, []) = FZero",
     "FTerm_cons(TFSucc, [M]) = FSucc(M)"];

val FArity_eqns = map (fn s =>
                           prove_goalw FNumber.thy 
                           ([FArity_def]@FTag.con_defs) s
                           (fn prems => [simp_tac nth_ss 1,
                                         simp_tac sum_ss 1]))
    ["FArity(TFZero) = 0",
     "FArity(TFSucc) = 1"];

val FOcc_eqns = map (fn s => prove_goalw FNumber.thy
                     [FOcc_def] s
                     (fn prems => 
                      [simp_tac (ZF_ss addsimps FNum_rec_eqns) 1]))
    ["FOcc(FZero) = Occ_cons(TFZero, [])",
     "FOcc(FSucc(M)) = Occ_cons(TFSucc, [FOcc(M)])"];

val FNum_Term_cons_intrs = map (fn s => prove_goal FNumber.thy s
                                 (fn prems =>
                                  [(cut_facts_tac prems 1),
                                   (asm_simp_tac 
                                    (IFOL_ss addsimps FTerm_cons_eqns) 1),
                                   (REPEAT (ares_tac FNum.intrs 1))]))
    ["FTerm_cons(TFZero, []): FNum",
     "M: FNum ==> FTerm_cons(TFSucc, [M]): FNum"];

val FArity_type = prove_goal FNumber.thy
    "T: FTag ==> FArity(T): nat"
  (fn [prem] =>
   [(rtac (prem RS FTag.elim) 1),
    (ALLGOALS hyp_subst_tac),
    (ALLGOALS (asm_simp_tac (list_ss addsimps FArity_eqns)))]);
    
val FNum_Occ_cons_cond = prove_goal FNumber.thy
    "Occ_cons_cond(FNum, FOcc, FTag, FArity)"
  (fn _ =>
    [(rtac Occ_cons_condI 1),
     (ALLGOALS (etac FTag.elim)),
     (ALLGOALS hyp_subst_tac),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps FArity_eqns))),
     (ALLGOALS (REPEAT o (eresolve_tac [bexE, conjE]))),
     (ALLGOALS (fn i=>
              (REPEAT
               (((etac length_0E i) THEN (atac i) THEN 
                 (hyp_subst_tac i)) ORELSE
                ((etac nth_0E i) THEN (atac i) THEN
                 (asm_simp_tac nth_ss i) THEN
                 (hyp_subst_tac i) THEN 
                 (asm_full_simp_tac nth_ss i)))))),
     (ALLGOALS (fn i=>
                ((rtac bexI i) THEN
                 (resolve_tac FOcc_eqns i) THEN
                 (type_auto_tac FNum.intrs [] i))))]);

val FNum_Occ_ind_cond = prove_goal FNumber.thy
    "Occ_ind_cond(FNum, FOcc, FTag, FArity, FTerm_cons)"
  (fn _ =>
    [(rtac Occ_ind_condI 1),
     (etac FNum.induct 1),
     (ALLGOALS (fn i =>
              (dtac bspec i) THEN (dtac bspec (i + 1)) THEN
              (dtac mp (i + 2)) THEN 
              (eresolve_tac (FTerm_cons_eqns RL [subst]) (i + 3)))),
     (TRYALL (type_auto_tac (list_typechecks @ FTag.intrs) [])),
     (ALLGOALS (asm_simp_tac (nth_ss addsimps (FTerm_cons_eqns @
                                             FArity_eqns @
                                             FOcc_eqns)))),
     (ALLGOALS (type_auto_tac FNum.intrs []))]);

val FNum_Term_cons_inj_cond = prove_goal FNumber.thy
    "Term_cons_inj_cond(FNum, FTag, FArity, FTerm_cons)"
  (fn _ =>
    [(rtac Term_cons_inj_condI 1),
     (rtac iffI 1),
     (REPEAT (CHANGED (TRYALL (etac FTag.elim)))),
     (ALLGOALS (REPEAT o hyp_subst_tac)),
     (ALLGOALS (asm_full_simp_tac (sum_ss addsimps
                                 [FTerm_cons_def, FArity_def]
                                 addsimps FTag.con_defs
                                 addsimps FNum.con_defs)))]);

local
    val prems = [FNum_Occ_cons_cond, FNum_Occ_ind_cond,
                 FNum_Term_cons_inj_cond,
                 FOccinv_def, FSub_def, Fsubterm_def,
                 Fgraft_def];

    fun RS_a_prem src dest m n = if m >= n then dest else
        (src RSN (m, dest)) handle THM(s, i, l) =>
            RS_a_prem src dest (m + 1) n ;

    fun th_apply (a::l) th = th_apply l 
        (RS_a_prem a th 1 (length (prems_of th)))
      | th_apply [] th = th;
in
    fun FNum_use_thm th = th_apply prems th
end;

val FNum_Term_cons_typechecks = nth_typechecks
    @ FNum_Term_cons_intrs @ FTag.intrs @ 
    [FArity_type, FNum_use_thm Occ_ind_cond_Occ_domain,
     FNum_use_thm Occ_ind_cond_Occ_in_Occ_range, PowI, succI1, succI2,
     consI1, consI2];

val FNum_Term_cons_ss = nth_ss 
    addsimps (FTerm_cons_eqns RL [sym])
    addsimps FArity_eqns
    setsolver (type_auto_tac FNum_Term_cons_typechecks);

structure FNumOcc = struct
    structure Tag = FTag;

    val con_defs = [FNum_rec_def, FOcc_def, FArity_def, FTerm_cons_def,
                    FOccinv_def, FSub_def, Fsubterm_def, Fgraft_def];

    val ind_tac = FNum_ind_tac;
    val rec_type = FNum_rec_type;
    val rec_eqns = FNum_rec_eqns;

    val Arity_type = FArity_type;
    val Term_cons_intrs = FNum_Term_cons_intrs;

    val Term_cons_eqns = FTerm_cons_eqns;
    val Arity_eqns = FArity_eqns;
    val Occ_eqns = FOcc_eqns;

    val Occ_cons_cond = FNum_Occ_cons_cond;
    val Occ_ind_cond = FNum_Occ_ind_cond;
    val Term_cons_inj_cond = FNum_Term_cons_inj_cond;
    val props = [FNum_Occ_cons_cond, FNum_Occ_ind_cond,
                 FNum_Term_cons_inj_cond,
                 FOccinv_def, FSub_def, Fsubterm_def,
                 Fgraft_def];
    val use_thm = FNum_use_thm;

    val Term_cons_typechecks = FNum_Term_cons_typechecks;
    val Term_cons_ss = FNum_Term_cons_ss;
end;

val FOcc_domain = FNumOcc.use_thm Occ_ind_cond_Occ_domain;
val FOcc_in_Occ_range = FNumOcc.use_thm Occ_ind_cond_Occ_in_Occ_range;

qed_goal "FOcc_FZeroE" FNumber.thy
    "[| u: FOcc(FZero); \
\       u = <[], TFZero> ==> R \
\    |] ==> R"
  (fn [major, prem] =>
    [(cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps FNumOcc.Occ_eqns) 1),
     (etac Occ_consE 1),
     (etac prem 1),
     (asm_full_simp_tac (IFOL_ss addsimps [length_Nil]) 1),
     (etac emptyE 1)]);

qed_goal "FOcc_FSuccE" FNumber.thy
    "[| u: FOcc(FSucc(M)); \
\       u = <[], TFSucc> ==> R; \
\       !! l T. [| u = <Cons(0, l), T>; <l, T>: FOcc(M) |] ==> R \
\    |] ==> R"
  (fn [major, prem1, prem2] =>
    [(cut_facts_tac [major] 1),
     (asm_full_simp_tac (IFOL_ss addsimps FNumOcc.Occ_eqns) 1),
     (etac Occ_consE 1),
     (etac prem1 1),
     (asm_full_simp_tac list_ss 1),
     (etac succE 1),
     (etac emptyE 2),
     (rtac prem2 1),
     (ALLGOALS (REPEAT o hyp_subst_tac)),
     (asm_full_simp_tac nth_ss 2),
     (rtac refl 1)]);

val FOcc_FNumEs = [FOcc_FZeroE, FOcc_FSuccE];

val FOcc_FNumIs = map (fn s => prove_goal FNumber.thy s
                         (fn prems =>
                          [(cut_facts_tac prems 1),
                           (asm_simp_tac 
                            (IFOL_ss addsimps FNumOcc.Occ_eqns) 1),
                           (resolve_tac [Occ_consI2, Occ_consI1] 1),
                           (IF_UNSOLVED (ALLGOALS (asm_simp_tac nth_ss))),
                           (IF_UNSOLVED (REPEAT 
                                         (ares_tac [succI1, succI2] 1)))]))
    ["<[], TFZero>: FOcc(FZero)",
     "<[], TFSucc>: FOcc(FSucc(M))",
     "<l, T>: FOcc(M) ==> <Cons(0, l), T>: FOcc(FSucc(M))"];

qed_goalw "FZO_FZero" FNumber.thy [FZO_def]
    "FZO(FZero) = {<[], TFZero>}"
  (fn _ =>
    [(asm_simp_tac (ZF_ss addsimps FNumOcc.Occ_eqns
		  addsimps [Occ_cons_Nil]) 1),
     (fast_tac eq_cs 1)]);

qed_goalw "FZO_FSucc" FNumber.thy [FZO_def]
    "FZO(FSucc(M)) = Occ_shift(0, FZO(M))"
  (fn _ =>
    [(asm_simp_tac (ZF_ss addsimps FNumOcc.Occ_eqns
		  addsimps [Occ_cons_Nil]) 1),
     (rtac equalityI 1),
     (safe_tac (ZF_cs addSEs [Occ_consE2, Occ_shiftE]
	      addSEs FNumOcc.Tag.free_SEs)),
     (rtac Occ_consI2 3),
     (rtac exI 5),
     (rtac refl 5),
     (REPEAT (ares_tac ([singletonI] @ list.intrs) 1)),
     (ALLGOALS (asm_full_simp_tac nth_ss)),
     (rtac Occ_shiftI 1),
     (fast_tac ZF_cs 1)]);

val FZO_eqns = [FZO_FZero, FZO_FSucc];

qed_goalw "Incomparable_FZO" FNumber.thy [FZO_def]
    "M: FNum ==> Incomparable(domain(FZO(M)))"
  (fn [prem] =>
    [(rtac Incomparable_subset 1),
     (rtac Incomparable_CorrectArity_0 1),
     (rtac (prem RS FOcc_domain) 1),
     (rtac (prem RS FOcc_in_Occ_range RS Occ_range_DenseTreeD) 1),
     (rtac domain_mono 1),
     (safe_tac ZF_cs),
     (dtac (prem RS FOcc_domain RS subsetD) 1),
     (etac SigmaE2 1),
     (dtac (prem RS FOcc_in_Occ_range RS Occ_range_CorrectArityD) 1),
     (asm_full_simp_tac (ZF_ss addsimps FNumOcc.Arity_eqns) 1)]);

qed_goal "FZO_FSucc_not_Nil" FNumber.thy
    "domain(FZO(FSucc(M))) ~= {[]}"
  (fn _ =>
    [(ALLGOALS (asm_simp_tac (IFOL_ss addsimps FZO_eqns))),
     (ALLGOALS (rtac notI)),
     (ALLGOALS (dtac (equalityD2 RS singleton_subsetD))),
     (ALLGOALS (fast_tac (ZF_cs addSEs list.free_SEs
                        addSEs [Occ_shiftE])))]);

qed_goalw "FZO_subset_FOcc" FNumber.thy [FZO_def]
    "FZO(M) <= FOcc(M)"
  (fn _ =>
    [(rtac Collect_subset 1)]);

qed_goalw "Fadd_type" FNumber.thy [Fadd_def]
    "[| M: FNum; N: FNum |] ==> Fadd(M,N): FNum"
  (fn [prem1, prem2] =>
    [(rtac (FNumOcc.use_thm def_graft_type) 1),
     (REPEAT (ares_tac [prem1, prem2, Incomparable_FZO, domain_mono,
                      FZO_subset_FOcc] 1))]);

qed_goalw "Fadd_FZero" FNumber.thy [Fadd_def]
    "N: FNum ==> Fadd(FZero, N) = N"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (asm_simp_tac (IFOL_ss addsimps FZO_eqns) 1),
     (asm_simp_tac (FNumOcc.Term_cons_ss addsimps 
          [domain_cons, domain_0, FNumOcc.use_thm def_graft_Nil]) 1)]);

qed_goalw "Fadd_FSucc" FNumber.thy [Fadd_def]
    "[| M: FNum; N: FNum |] ==> \
\        Fadd(FSucc(M), N) = FSucc(Fadd(M, N))"
  (fn prems =>
    [(cut_facts_tac prems 1),
     (subgoals_tac ["domain(FZO(FSucc(M))) ~= {[]}",
                  "Incomparable(domain(FZO(FSucc(M))))",
                  "domain(FZO(FSucc(M))) <= domain(FOcc(FSucc(M)))",
                  "FZO(M) <= list(nat) * FTag"] 1),
     (asm_full_simp_tac (IFOL_ss addsimps FZO_eqns) 1),
     (asm_full_simp_tac (FNumOcc.Term_cons_ss addsimps 
                  [lists_subtree_domain_eq, FNumOcc.use_thm def_graft]
                       addsimps Occ_subtree_simps) 1),
     (rtac (FZO_subset_FOcc RS subset_trans) 1),
     (REPEAT (ares_tac ([FOcc_domain, FZO_subset_FOcc, domain_mono, 
                       Incomparable_FZO, FZO_FSucc_not_Nil]
                      @ FNum.intrs) 1))]);

val Fsubterm_eqns = [FNumOcc.use_thm def_subterm_Nil] @
    (map (fn s => prove_goal FNumber.thy s
          (fn prems =>
           [(cut_facts_tac prems 1),
            (asm_simp_tac (FNumOcc.Term_cons_ss addsimps 
                           [FNumOcc.use_thm def_subterm_Cons]) 1)]))
     ["[| M: FNum; l: list(nat) |] ==> \
      \       Fsubterm(FSucc(M), Cons(0, l)) = Fsubterm(M, l)"]);

val Faddr_eqns = map (fn s => prove_goalw FNumber.thy [Faddr_def] s
    (fn prems => 
     [(asm_simp_tac (ZF_ss addsimps (prems@FNumOcc.rec_eqns)) 1)]))
    ["Faddr(FZero) = []",
     "Faddr(FSucc(M)) = Cons(0, Faddr(M))"];

qed_goalw "Faddr_type" FNumber.thy [Faddr_def]
    "M: FNum ==> Faddr(M): list(nat)"
  (fn [major] =>
    [(rtac (major RS FNumOcc.rec_type) 1),
     (REPEAT (ares_tac (list.intrs @ [nat_0I]) 1))]);

qed_goalw "Fdiff_FZero" FNumber.thy [Fdiff_def]
    "!!M. M: FNum ==> Fdiff(M, FZero) = M"
  (fn _ =>
    [(asm_simp_tac (IFOL_ss addsimps Fsubterm_eqns addsimps Faddr_eqns) 1)]);

qed_goalw "Fdiff_FSucc_FSucc" FNumber.thy [Fdiff_def]
    "!!M. [| M: FNum; N: FNum |] ==> Fdiff(FSucc(M), FSucc(N)) = Fdiff(M, N)"
  (fn _ =>
    [(asm_simp_tac (IFOL_ss addsimps Fsubterm_eqns addsimps Faddr_eqns
		  addsimps [Faddr_type]) 1)]);

