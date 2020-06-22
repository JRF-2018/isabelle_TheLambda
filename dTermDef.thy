(*
    File:        dTermDef.thy
    Time-stamp:  <2020-06-22T04:14:01Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory dTermDef imports ZF.Sum ZF.Nat Nth SubOcc LVariable begin

consts
  dTerm :: i
  dTag :: i

datatype
  dTerm = dVar( "x: LVariable" )
        | dBound( "n: nat" )
        | dLam( "M: dTerm" )
        | dApp( "M: dTerm", "N: dTerm")

datatype
  dTag = TdVar( "x: LVariable" )
       | TdBound( "n: nat" )
       | TdLam
       | TdApp

definition dArity :: "i=>i" where
"dArity(T) == dTag_case(%z. 0, %z. 0, 1, 2, T)"

definition dTerm_cons :: "[i, i]=>i" where
"dTerm_cons(T, l) = dTag_case(%z. dVar(z), %z. dBound(z),
                      dLam(nth(0, l)), dApp(nth(0, l), nth(1, l)), T)"

definition dOcc :: "i=>i" where
"dOcc(M) == dTerm_rec(
            %x. Occ_cons(TdVar(x), []),
            %n. Occ_cons(TdBound(n), []),
            %N r. Occ_cons(TdLam, [r]),
            %M N rm rn. Occ_cons(TdApp, [rm, rn]), M)"

definition dOccinv :: "i=>i" where
"dOccinv(x) == THE M. M: dTerm & x = dOcc(M)"

definition dSub :: "i=>i" where
"dSub(M) == {<l, dOccinv(Occ_Subtree(l, dOcc(M)))>. <l, T>: dOcc(M)}"

definition dsubterm :: "[i, i]=>i" where
"dsubterm(M, l) == THE N. <l, N>: dSub(M)"


lemma dTerm_rec_type:
  assumes "M: dTerm"
  and "!!x. [| x: LVariable |] ==> c(x): C(dVar(x))"
  and "!!n. [| n: nat |] ==> b(n): C(dBound(n))"
  and "!!M r. [| M: dTerm;  r: C(M) |] ==>
                   h(M,r): C(dLam(M))"
  and "!!M N rm rn. [| M: dTerm;  N: dTerm;
           rm: C(M); rn: C(N) |] ==> k(M,N,rm,rn): C(dApp(M,N))"
  shows "dTerm_rec(c,b,h,k,M) : C(M)"
apply (rule assms(1) [THEN dTerm.induct])
apply (simp_all add: assms)
done

lemma dTerm_cons_eqns:
  "dTerm_cons(TdVar(x), []) = dVar(x)"
  "dTerm_cons(TdBound(n), []) = dBound(n)"
  "dTerm_cons(TdLam, [M]) = dLam(M)"
  "dTerm_cons(TdApp, [M, N]) = dApp(M, N)"
apply (simp_all add: dTerm_cons_def)
done

lemma dArity_eqns:
  "dArity(TdVar(x)) = 0"
  "dArity(TdBound(n)) = 0"
  "dArity(TdLam) = 1"
  "dArity(TdApp) = 2"
apply (simp_all add: dArity_def)
done

lemma dOcc_eqns:
  "dOcc(dVar(x)) = Occ_cons(TdVar(x), [])"
  "dOcc(dBound(n)) = Occ_cons(TdBound(n), [])"
  "dOcc(dLam(M)) = Occ_cons(TdLam, [dOcc(M)])"
  "dOcc(dApp(M, N)) = Occ_cons(TdApp, [dOcc(M), dOcc(N)])"
apply (simp_all add: dOcc_def)
done

lemma dTerm_Term_cons_intrs:
  "x: LVariable ==> dTerm_cons(TdVar(x), []): dTerm"
  "n: nat ==> dTerm_cons(TdBound(n), []): dTerm"
  "[| M: dTerm |] ==> dTerm_cons(TdLam, [M]): dTerm"
  "[| M: dTerm; N: dTerm |] ==> dTerm_cons(TdApp, [M, N]): dTerm"
apply (simp_all add: dTerm_cons_eqns)
apply (assumption | rule dTerm.intros)+
done

lemma dArity_type:
  "T: dTag ==> dArity(T): nat"
apply (erule dTag.cases)
apply (simp_all add: dArity_eqns)
done

lemma dTerm_Occ_cons_cond:
  "Occ_cons_cond(dTerm, dOcc, dTag, dArity)"
apply (rule Occ_cons_condI)
apply (elim dTag.cases)
apply (simp_all add: dArity_eqns)
apply (elim dTag.cases)
apply (simp_all add: dArity_eqns)

apply (rule bexI)
apply (rule dOcc_eqns)
apply (typecheck add: dTerm.intros)

apply (rule bexI)
apply (rule dOcc_eqns)
apply (typecheck add: dTerm.intros)

apply (elim bexE conjE)
apply (erule nth_0E)
apply assumption
apply simp
apply simp
apply (rule bexI)
apply (rule dOcc_eqns)
apply (typecheck add: dTerm.intros)

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
apply (rule dOcc_eqns)
apply (typecheck add: dTerm.intros)
done

lemma dTerm_Occ_ind_cond:
  "Occ_ind_cond(dTerm, dOcc, dTag, dArity, dTerm_cons)"
apply (rule Occ_ind_condI)
apply (erule dTerm.induct)

apply (drule bspec)
apply (drule_tac [2] bspec)
apply (drule_tac [3] mp)
apply (erule_tac [4] dTerm_cons_eqns [THEN subst])
apply (typecheck add: dTag.intros)
apply (simp add: dTerm_cons_eqns dArity_eqns dOcc_eqns)
apply (typecheck add: dTerm.intros)

apply (drule bspec)
apply (drule_tac [2] bspec)
apply (drule_tac [3] mp)
apply (erule_tac [4] dTerm_cons_eqns [THEN subst])
apply (typecheck add: dTag.intros)
apply (simp add: dTerm_cons_eqns dArity_eqns dOcc_eqns)
apply (typecheck add: dTerm.intros)

apply (drule bspec)
apply (drule_tac [2] bspec)
apply (drule_tac [3] mp)
apply (erule_tac [4] dTerm_cons_eqns [THEN subst])
apply (typecheck add: dTag.intros)
apply (simp add: dTerm_cons_eqns dArity_eqns dOcc_eqns)
apply (typecheck add: dTerm.intros)

apply (drule bspec)
apply (drule_tac [2] bspec)
apply (drule_tac [3] mp)
apply (erule_tac [4] dTerm_cons_eqns [THEN subst])
apply (typecheck add: dTag.intros)
apply (simp add: dTerm_cons_eqns dArity_eqns dOcc_eqns)
apply (typecheck add: dTerm.intros)

done

lemma dTerm_Term_cons_inj_cond:
  "Term_cons_inj_cond(dTerm, dTag, dArity, dTerm_cons)"
apply (rule Term_cons_inj_condI)
apply (rule iffI)
apply (elim dTag.cases)
prefer 17
apply (elim dTag.cases)
apply (simp_all add: dTerm_cons_def dArity_def)
done

lemmas dTerm_Term_cons_typechecks = (* nth_typechecks *)
    dTerm_Term_cons_intrs dTag.intros 
    dArity_type Occ_ind_cond_Occ_domain [OF dTerm_Occ_ind_cond]
    Occ_ind_cond_Occ_in_Occ_range [OF dTerm_Occ_ind_cond]
    PowI succI1 succI2 (* consI1 *)consI2 (* nat_0I nat_succI *)

declare dTerm_Term_cons_typechecks [TC]

lemmas dTerm_Term_cons_simps = dArity_eqns (* dTerm_cons_eqns [THEN sym] *)

declare dTerm_Term_cons_simps [simp]

lemmas dTerm_cons_eqns_sym = dTerm_cons_eqns [THEN sym]

end
