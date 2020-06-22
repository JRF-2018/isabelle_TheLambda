(*
    File:        LTermDef.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open LTermDef;

local
    val con_defs = [TLVar_def, TLLam_def, TLApp_def];
    val con_iffs = con_defs RL [Ind_Syntax.def_swap_iff];
    structure Su = Standard_Sum;
    structure Pr = Standard_Prod;
    val free_SEs = Ind_Syntax.mk_free_SEs con_iffs @ Su.free_SEs
in
    structure LTag = 
	struct
	val con_defs = con_defs @ [LTag_def]
		
	val free_iffs = con_iffs @ 
	    [Su.distinct, Su.distinct', Su.inl_iff, Su.inr_iff, Pr.pair_iff];
	  
	val free_SEs = free_SEs;

	fun mk_free s =
	    prove_goalw LTermDef.thy con_defs s
	    (fn prems => [cut_facts_tac prems 1, 
			  fast_tac (sum_cs addSEs free_SEs) 1]);

	val intrs = map mk_free ["x: LVariable ==> TLVar(x): LTag",
				 "x: LVariable ==> TLLam(x): LTag",
				 "TLApp: LTag"];
	exception Nth;
	fun nth(a::b, s) = if s = 0 then  a
                          else if s > 0 then nth(b, s - 1) else raise Nth
          | nth([], s) = raise Nth;

        val elim = prove_goalw LTermDef.thy con_defs
            "[| T: LTag; \
\               !!x. [| x: LVariable; T = TLVar(x) |] ==> P;\
\               !!x. [| x: LVariable; T = TLLam(x) |] ==> P;\
\               !!x. [| T = TLApp |] ==> P \
\            |] ==> P"
            (fn major::prems =>
             [(cut_facts_tac [major] 1),
              (REPEAT (CHANGED (TRYALL (etac sumE)))),
              (ALLGOALS (fn i=>(rtac (nth(prems, i - 1)) i))),
              (ALLGOALS (fast_tac sum_cs))]);
        end
end;

fun LTerm_ind_tac term prems i = 
    EVERY [res_inst_tac [("x",term)] LTerm.induct i,
           ares_tac prems i];

val LTerm_rec_eqns = map (fn s => prove_goal LTermDef.thy s
                          (fn prems=>
                           [(rtac (LTerm_rec_def RS def_Vrec RS trans) 1),
                            (simp_tac (rank_ss addsimps LTerm.con_defs)  1)]))
    ["LTerm_rec(LVar(x), case_var, case_fun, case_app) = case_var(x)",
     "LTerm_rec(LLam(x,M), case_var, case_fun, case_app)\
\           = case_fun(x,M, LTerm_rec(M, case_var, case_fun, case_app))",
     "LTerm_rec(LApp(M,N), case_var, case_fun, case_app)\
\            = case_app(M,N,\
\                        LTerm_rec(M, case_var, case_fun, case_app),\
\                        LTerm_rec(N, case_var, case_fun, case_app))"];

(*Type checking -- proved by induction, as usual*)
val LTerm_rec_type = prove_goal LTermDef.thy
    "[| M: LTerm;    \
\       !!x. [| x: LVariable |] ==> c(x): C(LVar(x));   \
\       !!x M r. [| x:LVariable;  M: LTerm;  r: C(M) |] ==> \
\                    h(x,M,r): C(LLam(x,M));  \
\       !!x M N rm rn. [| M: LTerm;  N: LTerm;\
\            rm: C(M); rn: C(N) |] ==> k(M,N,rm,rn): C(LApp(M,N))  \
\    |] ==> LTerm_rec(M,c,h,k) : C(M)"
  (fn prems =>
    [(LTerm_ind_tac "M" prems 1),
     (ALLGOALS (asm_simp_tac (ZF_ss addsimps
                 (prems@LTerm_rec_eqns))))]);

val LTerm_cons_eqns = map (fn s =>
                           prove_goalw LTermDef.thy 
                           ([LTerm_cons_def]@LTag.con_defs) s
                           (fn prems => [simp_tac nth_ss 1,
                                         simp_tac sum_ss 1]))
    ["LTerm_cons(TLVar(x), []) = LVar(x)",
     "LTerm_cons(TLLam(x), [M]) = LLam(x, M)",
     "LTerm_cons(TLApp, [M, N]) = LApp(M, N)"];

val LArity_eqns = map (fn s =>
                           prove_goalw LTermDef.thy 
                           ([LArity_def]@LTag.con_defs) s
                           (fn prems => [simp_tac nth_ss 1,
                                         simp_tac sum_ss 1]))
    ["LArity(TLVar(x)) = 0",
     "LArity(TLLam(x)) = 1",
     "LArity(TLApp) = 2"];

val LOcc_eqns = map (fn s => prove_goalw LTermDef.thy
                     [LOcc_def] s
                     (fn prems => 
                      [simp_tac (ZF_ss addsimps LTerm_rec_eqns) 1]))
    ["LOcc(LVar(x)) = Occ_cons(TLVar(x), [])",
     "LOcc(LLam(x, M)) = Occ_cons(TLLam(x), [LOcc(M)])",
     "LOcc(LApp(M, N)) = Occ_cons(TLApp, [LOcc(M), LOcc(N)])"];

val LTerm_Term_cons_intrs = map (fn s => prove_goal LTermDef.thy s
                                 (fn prems =>
                                  [(cut_facts_tac prems 1),
                                   (asm_simp_tac 
                                    (IFOL_ss addsimps LTerm_cons_eqns) 1),
                                   (REPEAT (ares_tac LTerm.intrs 1))]))
    ["x: LVariable ==> LTerm_cons(TLVar(x), []): LTerm",
     "[| x: LVariable;  M: LTerm |] ==> LTerm_cons(TLLam(x), [M]): LTerm",
     "[| M: LTerm; N: LTerm |] ==> LTerm_cons(TLApp, [M, N]): LTerm"];

val LArity_type = prove_goal LTermDef.thy
    "T: LTag ==> LArity(T): nat"
  (fn [prem] =>
   [(rtac (prem RS LTag.elim) 1),
    (ALLGOALS hyp_subst_tac),
    (ALLGOALS (asm_simp_tac (list_ss addsimps LArity_eqns)))]);
    
val LTerm_Occ_cons_cond = prove_goal LTermDef.thy
    "Occ_cons_cond(LTerm, LOcc, LTag, LArity)"
  (fn _ =>
    [(rtac Occ_cons_condI 1),
     (ALLGOALS (etac LTag.elim)),
     (ALLGOALS hyp_subst_tac),
     (ALLGOALS (asm_full_simp_tac (nth_ss addsimps LArity_eqns))),
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
                 (resolve_tac LOcc_eqns i) THEN
                 (type_auto_tac LTerm.intrs [] i))))]);

val LTerm_Occ_ind_cond = prove_goal LTermDef.thy
    "Occ_ind_cond(LTerm, LOcc, LTag, LArity, LTerm_cons)"
  (fn _ =>
    [(rtac Occ_ind_condI 1),
     (etac LTerm.induct 1),
     (ALLGOALS (fn i =>
              (dtac bspec i) THEN (dtac bspec (i + 1)) THEN
              (dtac mp (i + 2)) THEN 
              (eresolve_tac (LTerm_cons_eqns RL [subst]) (i + 3)))),
     (TRYALL (type_auto_tac (list_typechecks @ LTag.intrs) [])),
     (ALLGOALS (asm_simp_tac (nth_ss addsimps (LTerm_cons_eqns @
                                             LArity_eqns @
                                             LOcc_eqns)))),
     (ALLGOALS (type_auto_tac LTerm.intrs []))]);

val LTerm_Term_cons_inj_cond = prove_goal LTermDef.thy
    "Term_cons_inj_cond(LTerm, LTag, LArity, LTerm_cons)"
  (fn _ =>
    [(rtac Term_cons_inj_condI 1),
     (rtac iffI 1),
     (REPEAT (CHANGED (TRYALL (etac LTag.elim)))),
     (ALLGOALS (REPEAT o hyp_subst_tac)),
     (ALLGOALS (asm_full_simp_tac (sum_ss addsimps
                                 [LTerm_cons_def, LArity_def]
                                 addsimps LTag.con_defs
                                 addsimps LTerm.con_defs)))]);

local
    val prems = [LTerm_Occ_cons_cond, LTerm_Occ_ind_cond,
                 LTerm_Term_cons_inj_cond,
                 LOccinv_def, LSub_def, Lsubterm_def,
                 Lgraft_def];

    fun RS_a_prem src dest m n = if m >= n then dest else
        (src RSN (m, dest)) handle THM(s, i, l) =>
            RS_a_prem src dest (m + 1) n ;

    fun th_apply (a::l) th = th_apply l 
        (RS_a_prem a th 1 (length (prems_of th)))
      | th_apply [] th = th;
in
    fun LTerm_use_thm th = th_apply prems th
end;

val LTerm_Term_cons_typechecks = nth_typechecks
    @ LTerm_Term_cons_intrs @ LTag.intrs @ 
    [LArity_type, LTerm_use_thm Occ_ind_cond_Occ_domain,
     LTerm_use_thm Occ_ind_cond_Occ_in_Occ_range, PowI, succI1, succI2,
     consI1, consI2];

val LTerm_Term_cons_ss = nth_ss 
    addsimps (LTerm_cons_eqns RL [sym])
    addsimps LArity_eqns
    setsolver (type_auto_tac LTerm_Term_cons_typechecks);

structure LTermOcc = struct
    structure Tag = LTag;

    val con_defs = [LTerm_rec_def, LOcc_def, LArity_def, LTerm_cons_def,
                    LOccinv_def, LSub_def, Lsubterm_def, Lgraft_def];

    val ind_tac = LTerm_ind_tac;
    val rec_type = LTerm_rec_type;
    val rec_eqns = LTerm_rec_eqns;

    val Arity_type = LArity_type;
    val Term_cons_intrs = LTerm_Term_cons_intrs;

    val Term_cons_eqns = LTerm_cons_eqns;
    val Arity_eqns = LArity_eqns;
    val Occ_eqns = LOcc_eqns;

    val Occ_cons_cond = LTerm_Occ_cons_cond;
    val Occ_ind_cond = LTerm_Occ_ind_cond;
    val Term_cons_inj_cond = LTerm_Term_cons_inj_cond;
    val props = [LTerm_Occ_cons_cond, LTerm_Occ_ind_cond,
                 LTerm_Term_cons_inj_cond,
                 LOccinv_def, LSub_def, Lsubterm_def,
                 Lgraft_def];
    val use_thm = LTerm_use_thm;

    val Term_cons_typechecks = LTerm_Term_cons_typechecks;
    val Term_cons_ss = LTerm_Term_cons_ss;
end;
