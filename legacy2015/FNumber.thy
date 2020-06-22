(*
    File:        FNumber.thy
    Time-stamp:  <2016-01-02T14:34:40Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

(* An example theory about Occ. *)

theory FNumber imports Sum Nth OccGraft begin

consts
  FNum :: i
  FTag :: i

datatype FNum = FZero | FSucc("n: FNum")

datatype FTag = TFZero | TFSucc

definition FArity :: "i=>i" where
"FArity(T) == FTag_case(0, 1, T)"

definition FTerm_cons :: "[i, i]=>i" where
"FTerm_cons(T, l) == FTag_case(FZero, FSucc(nth(0, l)), T)"


definition FOcc :: "i=>i" where
"FOcc(M) == FNum_rec(Occ_cons(TFZero, []),
          %M r. Occ_cons(TFSucc, [r]), M)"

definition FOccinv :: "i=>i" where
"FOccinv(x) == THE M. M: FNum & x = FOcc(M)"

definition FSub :: "i=>i" where
"FSub(M) == {<l, FOccinv(Occ_Subtree(l, FOcc(M)))>. <l, T>: FOcc(M)}"

definition Fsubterm :: "[i, i]=>i" where
"Fsubterm(M, l) == THE N. <l, N>: FSub(M)"

definition Fgraft :: "[i, i, i]=>i" where
"Fgraft(x, W, y) == FOccinv(Occ_Graft(FOcc(x), W, FOcc(y)))"

definition FZO :: "i=>i" where
"FZO(M) == {u: FOcc(M). EX l. u = <l, TFZero>}"

definition Fadd :: "[i, i]=>i" where
"Fadd(M, N) == Fgraft(M, domain(FZO(M)), N)"

definition Faddr :: "i=>i" where
"Faddr(M) == FNum_rec([], %M r. Cons(0, r), M)"

definition Fdiff :: "[i, i]=>i" where
"Fdiff(M, N) == Fsubterm(M, Faddr(N))"


lemma FNum_rec_type:
  assumes "M: FNum"
  and "z: C(FZero)"
  and "!!M r. [| M: FNum;  r: C(M) |] ==>
                   h(M,r): C(FSucc(M))"
  shows "FNum_rec(z, h, M) : C(M)"
apply (rule assms(1) [THEN FNum.induct])
apply (simp_all add: assms)
done

lemma FTerm_cons_eqns:
  "FTerm_cons(TFZero, []) = FZero"
  "FTerm_cons(TFSucc, [M]) = FSucc(M)"
apply (simp_all add: FTerm_cons_def)
done

lemma FArity_eqns:
  "FArity(TFZero) = 0"
  "FArity(TFSucc) = 1"
apply (simp_all add: FArity_def)
done

lemma FOcc_eqns:
  "FOcc(FZero) = Occ_cons(TFZero, [])"
  "FOcc(FSucc(M)) = Occ_cons(TFSucc, [FOcc(M)])"
apply (simp_all add: FOcc_def)
done

lemma FNum_Term_cons_intrs:
  "FTerm_cons(TFZero, []): FNum"
  "M: FNum ==> FTerm_cons(TFSucc, [M]): FNum"
apply (simp_all add: FTerm_cons_eqns)
apply (assumption | rule FNum.intros)+
done

lemma FArity_type:
  "T: FTag ==> FArity(T): nat"
apply (erule FTag.cases)
apply (simp_all add: FArity_eqns)
done

lemma FNum_Occ_cons_cond:
  "Occ_cons_cond(FNum, FOcc, FTag, FArity)"
apply (rule Occ_cons_condI)
apply (erule FArity_type)
apply (erule FTag.cases)
apply (simp_all add: FArity_eqns)
apply (rule bexI)
apply (rule FOcc_eqns)
apply (rule FNum.intros)
apply (erule bexE)
apply (erule nth_0E)
apply assumption
apply simp
apply simp
apply (rule bexI)
apply (rule FOcc_eqns)
apply (assumption | rule FNum.intros)+
done

lemma FNum_Occ_ind_cond:
  "Occ_ind_cond(FNum, FOcc, FTag, FArity, FTerm_cons)"
apply (rule Occ_ind_condI)
apply (erule FNum.induct)

apply (drule bspec)
apply (drule_tac [2] bspec)
apply (drule_tac [3] mp)
apply (erule_tac [4] FTerm_cons_eqns [THEN subst])
apply (typecheck add: FTag.intros)
apply (simp add: FTerm_cons_eqns FArity_eqns FOcc_eqns)
apply (typecheck add: FNum.intros)

apply (drule bspec)
apply (drule_tac [2] bspec)
apply (drule_tac [3] mp)
apply (erule_tac [4] FTerm_cons_eqns [THEN subst])
apply (typecheck add: FTag.intros)
apply (simp add: FTerm_cons_eqns FArity_eqns FOcc_eqns)
apply (typecheck add: FNum.intros)

done

lemma FNum_Term_cons_inj_cond:
  "Term_cons_inj_cond(FNum, FTag, FArity, FTerm_cons)"
apply (rule Term_cons_inj_condI)
apply (rule iffI)
apply (elim FTag.cases)
apply (simp_all add: FTerm_cons_def FArity_def)
apply (elim FTag.cases)
apply (simp_all add: FTerm_cons_def FArity_def)
done

lemmas FNum_Term_cons_typechecks = (* nth_typechecks *)
  FNum_Term_cons_intrs FTag.intros
  Occ_ind_cond_Occ_domain [OF FNum_Occ_ind_cond]
  Occ_ind_cond_Occ_in_Occ_range [OF FNum_Occ_ind_cond]
  PowI succI1 succI2 (* consI1 consI2 *)

declare FNum_Term_cons_typechecks [TC]

lemmas FNum_Term_cons_simps = (* FTerm_cons_eqns [THEN sym] *) FArity_eqns
declare FNum_Term_cons_simps [simp]
lemmas FTerm_cons_eqns_sym = FTerm_cons_eqns [THEN sym]

lemmas FOcc_domain = Occ_ind_cond_Occ_domain [OF FNum_Occ_ind_cond]
lemmas FOcc_in_Occ_range = Occ_ind_cond_Occ_in_Occ_range [OF FNum_Occ_ind_cond]

lemma FOcc_FZeroE:
  assumes major: "u: FOcc(FZero)"
  and prem: "u = <[], TFZero> ==> R"
  shows "R"
apply (insert major)
apply (simp only: FOcc_eqns)
apply (erule Occ_consE)
apply (erule prem)
apply (simp only: length.simps)
apply (erule emptyE)
done

lemma FOcc_FSuccE:
  assumes major: "u: FOcc(FSucc(M))"
  and prem1: "u = <[], TFSucc> ==> R"
  and prem2: "!! l T. [| u = <Cons(0, l), T>; <l, T>: FOcc(M) |] ==> R"
  shows "R"
apply (insert major)
apply (simp only: FOcc_eqns)
apply (erule Occ_consE)
apply (erule prem1)
apply simp
apply (erule succE)
apply (erule_tac [2] emptyE)
apply (rule prem2)
apply hypsubst
apply (rule refl)
apply simp
done

lemmas FOcc_FNumEs = FOcc_FZeroE FOcc_FSuccE

lemma FOcc_FNumIs:
  "<[], TFZero>: FOcc(FZero)"
  "<[], TFSucc>: FOcc(FSucc(M))"
  "<l, T>: FOcc(M) ==> <Cons(0, l), T>: FOcc(FSucc(M))"
apply (simp_all only: FOcc_eqns)
apply (rule Occ_consI1 Occ_consI2)+
apply simp
apply simp
done

lemma FZO_FZero:
  "FZO(FZero) = {<[], TFZero>}"
apply (unfold FZO_def)
apply (simp add: FOcc_eqns Occ_cons_Nil)
apply blast
done

lemma FZO_FSucc:
  "FZO(FSucc(M)) = Occ_shift(0, FZO(M))"
apply (unfold FZO_def)
apply (simp add: FOcc_eqns Occ_cons_Nil)
apply (rule equalityI)
apply (safe elim!: Occ_consE2 Occ_shiftE)
apply simp_all
apply (rule singletonI)
apply (rule Occ_shiftI)
apply blast
apply (rule Occ_consI2)
apply simp
apply simp
done

lemmas FZO_eqns = FZO_FZero FZO_FSucc

lemma Incomparable_FZO:
  assumes prem: "M: FNum"
  shows "Incomparable(domain(FZO(M)))"
apply (unfold FZO_def)
apply (rule Incomparable_subset)
apply (rule Incomparable_CorrectArity_0)
apply (rule prem [THEN FOcc_domain])
apply (rule prem [THEN FOcc_in_Occ_range, THEN Occ_range_DenseTreeD])
apply (rule domain_mono)
apply safe
apply simp
apply (drule prem [THEN FOcc_domain, THEN subsetD])
apply (erule SigmaE2)
apply (drule prem [THEN FOcc_in_Occ_range, THEN Occ_range_CorrectArityD])
apply simp
done

lemma FZO_FSucc_not_Nil:
  "domain(FZO(FSucc(M))) ~= {[]}"
apply (simp add: FZO_eqns)
apply (rule notI)
apply (drule equalityD2 [THEN singleton_subsetD])
apply (safe elim!: Occ_shiftE)
apply simp
done

lemma FZO_subset_FOcc:
  "FZO(M) <= FOcc(M)"
apply (unfold FZO_def)
apply (rule Collect_subset)
done

lemmas FNum_def_graft_type = def_graft_type [OF FNum_Occ_cons_cond FNum_Occ_ind_cond
     FOccinv_def Fgraft_def]

lemma Fadd_type:
  "[| M: FNum; N: FNum |] ==> Fadd(M,N): FNum"
apply (unfold Fadd_def)
apply (rule FNum_def_graft_type)
apply (assumption | rule Incomparable_FZO domain_mono
                          FZO_subset_FOcc)+
done

lemmas FNum_def_graft_Nil = 
  def_graft_Nil [OF FNum_Occ_cons_cond FNum_Occ_ind_cond
    FOccinv_def Fgraft_def]

lemma Fadd_FZero:
  "N: FNum ==> Fadd(FZero, N) = N"
apply (unfold Fadd_def)
apply (simp only: FZO_eqns)
apply (simp add: FNum_def_graft_Nil FTerm_cons_eqns_sym)
done

lemmas FNum_def_graft = def_graft [OF
   FNum_Occ_cons_cond FNum_Occ_ind_cond 
   FNum_Term_cons_inj_cond FOccinv_def Fgraft_def]

lemma Fadd_FSucc:
  "[| M: FNum; N: FNum |] ==>
       Fadd(FSucc(M), N) = FSucc(Fadd(M, N))"
apply (unfold Fadd_def)
apply (subgoal_tac "domain(FZO(FSucc(M))) ~= {[]}"
         "Incomparable(domain(FZO(FSucc(M))))"
         "domain(FZO(FSucc(M))) <= domain(FOcc(FSucc(M)))"
         "FZO(M) <= list(nat) * FTag")
apply (simp only: FZO_eqns)
apply (simp add: FTerm_cons_eqns_sym lists_subtree_domain_eq
          FNum_def_graft Occ_subtree_simps)
apply (rule FZO_subset_FOcc [THEN subset_trans])
apply (assumption | rule FOcc_domain FZO_subset_FOcc domain_mono
        Incomparable_FZO FZO_FSucc_not_Nil FNum.intros)+
done

lemmas FNum_def_subterm_Nil = def_subterm_Nil [OF
   FNum_Occ_cons_cond FNum_Occ_ind_cond FOccinv_def FSub_def
   FNum_Term_cons_inj_cond Fsubterm_def]

lemmas FNum_def_subterm_Cons = def_subterm_Cons [OF
   FNum_Occ_cons_cond FNum_Occ_ind_cond FOccinv_def FSub_def
   FNum_Term_cons_inj_cond Fsubterm_def]

lemma Fsubterm_Cons:
  "[| M: FNum; l: list(nat) |] ==>
     Fsubterm(FSucc(M), Cons(0, l)) = Fsubterm(M, l)"
apply (simp add: FNum_def_subterm_Cons FTerm_cons_eqns_sym)
done

lemmas Fsubterm_eqns = FNum_def_subterm_Nil Fsubterm_Cons

lemma Faddr_eqns:
  "Faddr(FZero) = []"
  "Faddr(FSucc(M)) = Cons(0, Faddr(M))"
apply (unfold Faddr_def)
apply simp_all
done

lemma Faddr_type:
  "M: FNum ==> Faddr(M): list(nat)"
apply (unfold Faddr_def)
apply (erule FNum_rec_type)
apply (assumption | rule list.intros nat_0I)+
done

lemma Fdiff_FZero:
  "!!M. M: FNum ==> Fdiff(M, FZero) = M"
apply (unfold Fdiff_def)
apply (simp only: Fsubterm_eqns Faddr_eqns)
done

lemma Fdiff_FSucc_FSucc:
  "!!M. [| M: FNum; N: FNum |] ==> Fdiff(FSucc(M), FSucc(N)) = Fdiff(M, N)"
apply (unfold Fdiff_def)
apply (simp only: Fsubterm_eqns Faddr_eqns Faddr_type)
done

end
