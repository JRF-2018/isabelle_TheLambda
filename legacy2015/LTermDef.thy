(*
    File:        LTermDef.thy
    Time-stamp:  <2015-12-25T15:39:57Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory LTermDef imports Sum Nth OccGraft LVariable begin

consts
  LTerm :: i
  LTag :: i

datatype
  LTerm = LVar ( "x: LVariable" )
        | LLam ( "x: LVariable", "M: LTerm")
        | LApp ( "M: LTerm", "N: LTerm")

datatype
  LTag = TLVar ( "x: LVariable" )
       | TLLam ( "x: LVariable" )
       | TLApp

definition LArity :: "i=>i" where
"LArity(T) == LTag_case(%x. 0, %x. 1, 2, T)"

definition LTerm_cons :: "[i, i]=>i" where
"LTerm_cons(T, l) == LTag_case(%x. LVar(x),
                               %x. LLam(x, nth(0, l)),
                               LApp(nth(0, l), nth(1, l)), T)"

definition LOcc :: "i=>i" where
  "LOcc(M) == LTerm_rec(
            %x. Occ_cons(TLVar(x), []),
            %x N r. Occ_cons(TLLam(x), [r]),
            %M N rm rn. Occ_cons(TLApp, [rm, rn]), M)"

definition LOccinv :: "i=>i" where
"LOccinv(x) == THE M. M: LTerm & x = LOcc(M)"

definition LSub :: "i=>i" where
"LSub(M) == {<l, LOccinv(Occ_Subtree(l, LOcc(M)))>. <l, T>: LOcc(M)}"

definition Lsubterm :: "[i, i]=>i" where
"Lsubterm(M, l) == THE N. <l, N>: LSub(M)"

definition Lgraft :: "[i, i, i]=>i" where
"Lgraft(x, W, y) == LOccinv(Occ_Graft(LOcc(x), W, LOcc(y)))"

lemma LTerm_rec_type:
  assumes "M: LTerm"
  and "!!x. [| x: LVariable |] ==> c(x): C(LVar(x))"
  and "!!x M r. [| x:LVariable;  M: LTerm;  r: C(M) |] ==>
                   h(x,M,r): C(LLam(x,M))"
  and "!!x M N rm rn. [| M: LTerm;  N: LTerm;
         rm: C(M); rn: C(N) |] ==> k(M,N,rm,rn): C(LApp(M,N))"
  shows "LTerm_rec(c,h,k,M) : C(M)"
apply (rule assms(1) [THEN LTerm.induct])
apply (simp_all add: assms)
done

lemma LTerm_cons_eqns:
  "LTerm_cons(TLVar(x), []) = LVar(x)"
  "LTerm_cons(TLLam(x), [M]) = LLam(x, M)"
  "LTerm_cons(TLApp, [M, N]) = LApp(M, N)"
apply (simp_all add: LTerm_cons_def)
done

lemma LArity_eqns:
  "LArity(TLVar(x)) = 0"
  "LArity(TLLam(x)) = 1"
  "LArity(TLApp) = 2"
apply (simp_all add: LArity_def)
done

lemma LOcc_eqns:
  "LOcc(LVar(x)) = Occ_cons(TLVar(x), [])"
  "LOcc(LLam(x, M)) = Occ_cons(TLLam(x), [LOcc(M)])"
  "LOcc(LApp(M, N)) = Occ_cons(TLApp, [LOcc(M), LOcc(N)])"
apply (simp_all add: LOcc_def)
done

lemma LTerm_Term_cons_intrs:
  "x: LVariable ==> LTerm_cons(TLVar(x), []): LTerm"
  "[| x: LVariable;  M: LTerm |] ==> LTerm_cons(TLLam(x), [M]): LTerm"
  "[| M: LTerm; N: LTerm |] ==> LTerm_cons(TLApp, [M, N]): LTerm"
apply (simp_all add: LTerm_cons_eqns)
apply (assumption | rule LTerm.intros)+
done

lemma LArity_type:
  "T: LTag ==> LArity(T): nat"
apply (erule LTag.cases)
apply (simp_all add: LArity_eqns)
done

lemma LTerm_Occ_cons_cond:
  "Occ_cons_cond(LTerm, LOcc, LTag, LArity)"
apply (rule Occ_cons_condI)
apply (elim LTag.cases)
apply (simp_all add: LArity_eqns)
apply (elim LTag.cases)
apply (simp_all add: LArity_eqns)

apply (rule bexI)
apply (rule LOcc_eqns)
apply (typecheck add: LTerm.intros)

apply (elim bexE conjE)
apply (erule nth_0E)
apply assumption
apply simp
apply simp
apply (rule bexI)
apply (rule LOcc_eqns)
apply (typecheck add: LTerm.intros)

apply (elim bexE conjE)
apply (erule nth_0E)
apply assumption
apply simp
apply simp
apply (erule nth_0E)
apply assumption
apply simp
apply simp
apply (rule bexI)
apply (rule LOcc_eqns)
apply (typecheck add: LTerm.intros)
done

lemma LTerm_Occ_ind_cond:
  "Occ_ind_cond(LTerm, LOcc, LTag, LArity, LTerm_cons)"
apply (rule Occ_ind_condI)
apply (erule LTerm.induct)

apply (drule bspec)
apply (drule_tac [2] bspec)
apply (drule_tac [3] mp)
apply (erule_tac [4] LTerm_cons_eqns [THEN subst])
apply (typecheck add: LTag.intros)
apply (simp add: LTerm_cons_eqns LArity_eqns LOcc_eqns)
apply (typecheck add: LTerm.intros)

apply (drule bspec)
apply (drule_tac [2] bspec)
apply (drule_tac [3] mp)
apply (erule_tac [4] LTerm_cons_eqns [THEN subst])
apply (typecheck add: LTag.intros)
apply (simp add: LTerm_cons_eqns LArity_eqns LOcc_eqns)
apply (typecheck add: LTerm.intros)

apply (drule bspec)
apply (drule_tac [2] bspec)
apply (drule_tac [3] mp)
apply (erule_tac [4] LTerm_cons_eqns [THEN subst])
apply (typecheck add: LTag.intros)
apply (simp add: LTerm_cons_eqns LArity_eqns LOcc_eqns)
apply (typecheck add: LTerm.intros)

done

lemma LTerm_Term_cons_inj_cond:
  "Term_cons_inj_cond(LTerm, LTag, LArity, LTerm_cons)"
apply (rule Term_cons_inj_condI)
apply (rule iffI)
apply (elim LTag.cases)
prefer 10
apply (elim LTag.cases)
apply (simp_all add: LTerm_cons_def LArity_def)
done

lemmas LTerm_Term_cons_typechecks = (* nth_typechecks *)
    LTerm_Term_cons_intrs LTag.intros
    LArity_type Occ_ind_cond_Occ_domain [OF LTerm_Occ_ind_cond]
    Occ_ind_cond_Occ_in_Occ_range [OF LTerm_Occ_ind_cond]
    PowI succI1 succI2

declare LTerm_Term_cons_typechecks [TC]

lemmas LTerm_Term_cons_simps = LArity_eqns (* LTerm_cons_eqns [THEN sym] *)

declare LTerm_Term_cons_simps [simp]

lemmas LTerm_cons_eqns_sym = LTerm_cons_eqns [THEN sym]

end
