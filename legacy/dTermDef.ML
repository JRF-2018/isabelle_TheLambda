(*
    File:        dTermDef.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open dTermDef;

local
    val con_defs = [TdVar_def, TdBound_def, TdLam_def, TdApp_def];
    val con_iffs = con_defs RL [Ind_Syntax.def_swap_iff];
    structure Su = Standard_Sum;
    structure Pr = Standard_Prod;
    val free_SEs = Ind_Syntax.mk_free_SEs con_iffs @ Su.free_SEs
in
    structure dTag = 
        struct
        val con_defs = con_defs @ [dTag_def]
                
        val free_iffs = con_iffs @ 
            [Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff, Pr.pair_iff];
          
        val free_SEs = free_SEs;

        fun mk_free s =
            prove_goalw dTermDef.thy con_defs s
            (fn prems => [cut_facts_tac prems 1, 
                          fast_tac (sum_cs addSEs free_SEs) 1]);

        val intrs = map mk_free ["x: LVariable ==> TdVar(x): dTag",
                                 "n: nat ==> TdBound(n): dTag",
                                 "TdLam: dTag",
                                 "TdApp: dTag"];

        exception Nth;
        fun nth(a::b, s) = if s = 0 then  a
                          else if s > 0 then nth(b, s - 1) else raise Nth
          | nth([], s) = raise Nth;

        val elim = prove_goalw dTermDef.thy con_defs
            "[| T: dTag; \
\               !!x. [| x: LVariable; T = TdVar(x) |] ==> P;\
\               !!n. [| n: nat; T = TdBound(n) |] ==> P;\
\               [| T = TdLam |] ==> P;\
\               [| T = TdApp |] ==> P \
\            |] ==> P"
            (fn major::prems =>
             [(cut_facts_tac [major] 1),
              (REPEAT (CHANGED (TRYALL (etac sumE)))),
              (ALLGOALS (fn i=>(rtac (nth(prems, i - 1)) i))),
              (ALLGOALS (fast_tac sum_cs))]);
        end
end;

fun dTerm_ind_tac term prems i = 
    EVERY [res_inst_tac [("x",term)] dTerm.induct i,
           ares_tac prems i];

val dTerm_rec_eqns = map (fn s => prove_goal dTermDef.thy s
                          (fn prems=>
                           [(rtac (dTerm_rec_def RS def_Vrec RS trans) 1),
                            (simp_tac (rank_ss addsimps dTerm.con_defs)  1)]))
    ["dTerm_rec(dVar(x), case_var, case_bound, case_fun, case_app) \
\           = case_var(x)",
     "dTerm_rec(dBound(n), case_var, case_bound, case_fun, case_app) \
\           = case_bound(n)",
     "dTerm_rec(dLam(M), case_var, case_bound, case_fun, case_app)\
\       = case_fun(M, dTerm_rec(M, case_var, case_bound, case_fun, case_app))",
     "dTerm_rec(dApp(M,N), case_var, case_bound, case_fun, case_app)\
\           = case_app(M,N,\
\                   dTerm_rec(M, case_var, case_bound, case_fun, case_app),\
\                   dTerm_rec(N, case_var, case_bound, case_fun, case_app))"];

(*Type checking -- proved by induction, as usual*)
val dTerm_rec_type = prove_goal dTermDef.thy
    "[| M: dTerm;    \
\       !!x. [| x: LVariable |] ==> c(x): C(dVar(x));   \
\       !!n. [| n: nat |] ==> b(n): C(dBound(n));   \
\       !!M r. [| M: dTerm;  r: C(M) |] ==> \
\                    h(M,r): C(dLam(M));  \
\       !!M N rm rn. [| M: dTerm;  N: dTerm;\
\            rm: C(M); rn: C(N) |] ==> k(M,N,rm,rn): C(dApp(M,N))  \
\    |] ==> dTerm_rec(M,c,b,h,k) : C(M)"
  (fn prems =>
    [(dTerm_ind_tac "M" prems 1),
     (ALLGOALS (asm_simp_tac (ZF_ss addsimps
                 (prems@dTerm_rec_eqns))))]);

val dTerm_cons_eqns = map (fn s =>
                           prove_goalw dTermDef.thy 
                           ([dTerm_cons_def]@dTag.con_defs) s
                           (fn prems => [simp_tac nth_ss 1,
                                         simp_tac sum_ss 1]))
    ["dTerm_cons(TdVar(x), []) = dVar(x)",
     "dTerm_cons(TdBound(n), []) = dBound(n)",
     "dTerm_cons(TdLam, [M]) = dLam(M)",
     "dTerm_cons(TdApp, [M, N]) = dApp(M, N)"];

val dArity_eqns = map (fn s =>
                           prove_goalw dTermDef.thy 
                           ([dArity_def]@dTag.con_defs) s
                           (fn prems => [simp_tac nth_ss 1,
                                         simp_tac sum_ss 1]))
    ["dArity(TdVar(x)) = 0",
     "dArity(TdBound(n)) = 0",
     "dArity(TdLam) = 1",
     "dArity(TdApp) = 2"];

val dOcc_eqns = map (fn s => prove_goalw dTermDef.thy
                     [dOcc_def] s
                     (fn prems => 
                      [simp_tac (ZF_ss addsimps dTerm_rec_eqns) 1]))
    ["dOcc(dVar(x)) = Occ_cons(TdVar(x), [])",
     "dOcc(dBound(n)) = Occ_cons(TdBound(n), [])",
     "dOcc(dLam(M)) = Occ_cons(TdLam, [dOcc(M)])",
     "dOcc(dApp(M, N)) = Occ_cons(TdApp, [dOcc(M), dOcc(N)])"];

val dTerm_Term_cons_intrs = map (fn s => prove_goal dTermDef.thy s
                                 (fn prems =>
                                  [(cut_facts_tac prems 1),
                                   (asm_simp_tac 
                                    (IFOL_ss addsimps dTerm_cons_eqns) 1),
                                   (REPEAT (ares_tac dTerm.intrs 1))]))
    ["x: LVariable ==> dTerm_cons(TdVar(x), []): dTerm",
     "n: nat ==> dTerm_cons(TdBound(n), []): dTerm",
     "[| M: dTerm |] ==> dTerm_cons(TdLam, [M]): dTerm",
     "[| M: dTerm; N: dTerm |] ==> dTerm_cons(TdApp, [M, N]): dTerm"];

val dArity_type = prove_goal dTermDef.thy
    "T: dTag ==> dArity(T): nat"
  (fn [prem] =>
   [(rtac (prem RS dTag.elim) 1),
    (ALLGOALS hyp_subst_tac),
    (ALLGOALS (asm_simp_tac (list_ss addsimps dArity_eqns)))]);
    
val dTerm_Occ_cons_cond = prove_goal dTermDef.thy
    "Occ_cons_cond(dTerm, dOcc, dTag, dArity)"
  (fn _ =>
    [(rtac Occ_cons_condI 1),
     (ALLGOALS (etac dTag.elim)),
     (ALLGOALS hyp_subst_tac),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps dArity_eqns))),
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
               (resolve_tac dOcc_eqns i) THEN
               (type_auto_tac dTerm.intrs [] i))))]);

val dTerm_Occ_ind_cond = prove_goal dTermDef.thy
    "Occ_ind_cond(dTerm, dOcc, dTag, dArity, dTerm_cons)"
  (fn _ =>
    [(rtac Occ_ind_condI 1),
     (etac dTerm.induct 1),
     (ALLGOALS (fn i =>
              (dtac bspec i) THEN (dtac bspec (i + 1)) THEN
              (dtac mp (i + 2)) THEN 
              (eresolve_tac (dTerm_cons_eqns RL [subst]) (i + 3)))),
     (TRYALL (type_auto_tac (list_typechecks @ dTag.intrs) [])),
     (ALLGOALS (asm_simp_tac (nth_ss addsimps (dTerm_cons_eqns @
                                             dArity_eqns @
                                             dOcc_eqns)))),
     (ALLGOALS (type_auto_tac dTerm.intrs []))]);

val dTerm_Term_cons_inj_cond = prove_goal dTermDef.thy
    "Term_cons_inj_cond(dTerm, dTag, dArity, dTerm_cons)"
  (fn _ =>
    [(rtac Term_cons_inj_condI 1),
     (rtac iffI 1),
     (REPEAT (CHANGED (TRYALL (etac dTag.elim)))),
     (ALLGOALS (REPEAT o hyp_subst_tac)),
     (ALLGOALS (asm_full_simp_tac (sum_ss addsimps
                                 [dTerm_cons_def, dArity_def]
                                 addsimps dTag.con_defs
                                 addsimps dTerm.con_defs)))]);

local
    val prems = [dTerm_Occ_cons_cond, dTerm_Occ_ind_cond,
                 dTerm_Term_cons_inj_cond,
                 dOccinv_def, dSub_def, dsubterm_def];

    fun RS_a_prem src dest m n = if m >= n then dest else
        (src RSN (m, dest)) handle THM(s, i, l) =>
            RS_a_prem src dest (m + 1) n ;

    fun th_apply (a::l) th = th_apply l 
        (RS_a_prem a th 1 (length (prems_of th)))
      | th_apply [] th = th;
in
    fun dTerm_use_thm th = th_apply prems th
end;

val dTerm_Term_cons_typechecks = nth_typechecks
    @ dTerm_Term_cons_intrs @ dTag.intrs @ 
    [dArity_type, dTerm_use_thm Occ_ind_cond_Occ_domain,
     dTerm_use_thm Occ_ind_cond_Occ_in_Occ_range, PowI, succI1, succI2,
     consI1, consI2, nat_0I, nat_succI];

val dTerm_Term_cons_ss = nth_ss 
    addsimps (dTerm_cons_eqns RL [sym])
    addsimps dArity_eqns
    setsolver (type_auto_tac dTerm_Term_cons_typechecks);

structure dTermOcc = struct
    structure Tag = dTag;

    val con_defs = [dTerm_rec_def, dOcc_def, dArity_def, dTerm_cons_def,
                    dOccinv_def, dSub_def, dsubterm_def];

    val ind_tac = dTerm_ind_tac;
    val rec_type = dTerm_rec_type;
    val rec_eqns = dTerm_rec_eqns;

    val Arity_type = dArity_type;
    val Term_cons_intrs = dTerm_Term_cons_intrs;

    val Term_cons_eqns = dTerm_cons_eqns;
    val Arity_eqns = dArity_eqns;
    val Occ_eqns = dOcc_eqns;

    val Occ_cons_cond = dTerm_Occ_cons_cond;
    val Occ_ind_cond = dTerm_Occ_ind_cond;
    val Term_cons_inj_cond = dTerm_Term_cons_inj_cond;
    val props = [dTerm_Occ_cons_cond, dTerm_Occ_ind_cond,
                 dTerm_Term_cons_inj_cond,
                 dOccinv_def, dSub_def, dsubterm_def];

    val use_thm = dTerm_use_thm;

    val Term_cons_typechecks = dTerm_Term_cons_typechecks;
    val Term_cons_ss = dTerm_Term_cons_ss;
end;
