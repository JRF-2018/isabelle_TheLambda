(*
    File:        dLambda.thy
    Time-stamp:  <2016-01-05T12:38:20Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory dLambda imports dTermDef OCons FinCard Arith begin

definition dAbst :: "[i, i, i]=>i" where
"dAbst(M, x, n) == dTerm_rec(
       %y. lam i: nat. if(x=y, dBound(i), dVar(y)), 
       %j. lam i: nat. dBound(j),
       %N r. lam i: nat. dLam(r`succ(i)),
       %A B ra rb. lam i: nat. dApp(ra`i, rb`i), M) ` n"

definition dLift :: "[i, i]=>i" where
"dLift(M, n) == dTerm_rec(
       %x. lam i: nat. dVar(x),
       %j. lam i: nat. if (j < i, dBound(j), dBound(succ(j))),
       %N r. lam i: nat. dLam(r`succ(i)),
       %A B ra rb. lam i: nat. dApp(ra`i, rb`i), M) ` n"

definition dSubst :: "[i, i, i]=>i" where
"dSubst(M, n, N) == dTerm_rec(
       %x. lam i: nat. lam m: dTerm. dVar(x),
       %j. lam i: nat. lam m: dTerm. if (i < j, dBound(j #- 1),
                                      if (i=j, m, dBound(j))),
       %N r. lam i: nat. lam m: dTerm. dLam(r`succ(i)`dLift(m, 0)),
       %A B ra rb. lam i: nat. lam m: dTerm. dApp(ra`i`m, rb`i`m), M)`n`N"


definition dDeg :: "i=>i" where
"dDeg(M) == dTerm_rec(%x. 0, %n. succ(n), %N r. r #- 1,
                      %A B rm rn. rm Un rn, M)"

definition dFV :: "i=>i" where
"dFV(M) == {x: LVariable. EX l.  <l, TdVar(x)>: dOcc(M)}"

definition dProp :: i where
"dProp == {M: dTerm. dDeg(M) = 0}"


definition dLamDegBase :: "[i, i]=>i" where
"dLamDegBase(l, M) == {v: dOcc(M). EX m. v = <m, TdLam> & m ~= l &
                                   initseg(nat, m, l)}"

definition dLamDeg :: "[i, i]=>i" where
"dLamDeg(l, M) == |dLamDegBase(l, M)|"

definition dBoundBy :: "[i, i, i]=>o" where
"dBoundBy(u, v, M) == M: dTerm & u: dOcc(M) & v: dOcc(M) &
   (EX n l m x. u = <m, TdBound(n)> & v = <l, TdLam> &
     m = l @ x & dLamDeg(x, dsubterm(M, l)) = succ(n))"


lemmas dOcc_domain = Occ_ind_cond_Occ_domain [OF
  dTerm_Occ_ind_cond]

lemmas dOcc_in_Occ_range = Occ_ind_cond_Occ_in_Occ_range [OF
  dTerm_Occ_ind_cond]

lemma dOcc_typeD1:
  assumes major: "<l, T>: dOcc(M)"
  and prem: "M: dTerm"
  shows "l: list(nat)"
apply (rule major [THEN prem [THEN dOcc_domain, THEN subsetD, THEN SigmaD1]])
done

lemma dOcc_typeD2:
  assumes major: "<l, T>: dOcc(M)"
  and prem: "M: dTerm"
  shows "T: dTag"
apply (rule major [THEN prem [THEN dOcc_domain, THEN subsetD, THEN SigmaD2]])
done

lemma dTerm_typeEs:
  "[| dVar(x): dTerm; x: LVariable ==> R |] ==> R"
  "[| dBound(n): dTerm; n: nat ==> R |] ==> R"
  "[| dLam(M): dTerm; M: dTerm ==> R |] ==> R"
  "[| dApp(M, N): dTerm; [| M: dTerm; N: dTerm |] ==> R |] ==> R"
apply (erule dTerm.cases, (blast elim!: dTerm.free_elims)+)+
done

lemma dTag_typeEs:
  "[| TdVar(x): dTag; x: LVariable ==> R |] ==> R"
  "[| TdBound(n): dTag; n: nat ==> R |] ==> R"
apply (erule dTag.cases, (blast elim!: dTag.free_elims)+)+
done

lemma dOcc_dVarE:
  assumes major: "u: dOcc(dVar(x))"
  and prem: "u = <[], TdVar(x)> ==> R"
  shows "R"
apply (insert major)
apply (simp add: dOcc_eqns)
apply (erule Occ_consE)
apply (erule prem)
apply simp
done

lemma dOcc_dBoundE:
  assumes major: "u: dOcc(dBound(n))"
  and prem: "u = <[], TdBound(n)> ==> R"
  shows "R"
apply (insert major)
apply (simp only: dOcc_eqns)
apply (erule Occ_consE)
apply (erule prem)
apply simp
done

lemma dOcc_dLamE:
  assumes major: "u: dOcc(dLam(M))"
  and prem1: "u = <[], TdLam> ==> R"
  and prem2:
     "!! l T. [| u = <Cons(0, l), T>; <l, T>: dOcc(M) |] ==> R"
  shows "R"
apply (insert major)
apply (simp only: dOcc_eqns)
apply (erule Occ_consE)
apply (erule prem1)
apply simp
apply (erule succE)
apply (erule_tac [2] emptyE)
apply hypsubst
apply (rule prem2)
prefer 2 apply simp
apply assumption
done

lemma dOcc_dAppE:
  assumes major: "u: dOcc(dApp(M, N))"
  and prem1: "u = <[], TdApp> ==> R"
  and prem2:
     "!! l T. [| u = <Cons(0, l), T>; <l, T>: dOcc(M) |] ==> R"
  and prem3:
     "!! l T. [| u = <Cons(1, l), T>; <l, T>: dOcc(N) |] ==> R"
  shows "R"
apply (insert major)
apply (simp only: dOcc_eqns)
apply (erule Occ_consE)
apply (erule prem1)
apply simp
apply (erule succE)
apply (erule_tac [2] succE)
apply (erule_tac [3] emptyE)
apply hypsubst
apply (rule prem3)
prefer 2 apply simp
apply assumption
apply hypsubst
apply (rule prem2)
prefer 2 apply simp
apply assumption
done

lemmas dOcc_dTermEs = dOcc_dVarE dOcc_dBoundE dOcc_dLamE dOcc_dAppE

lemma dOcc_dTermIs:
  "<[], TdVar(x)>: dOcc(dVar(x))"
  "<[], TdBound(n)>: dOcc(dBound(n))"
  "<[], TdLam>: dOcc(dLam(M))"
  "<l, T>: dOcc(M) ==> <Cons(0, l), T>: dOcc(dLam(M))"
  "<[], TdApp>: dOcc(dApp(M, N))"
  "<l, T>: dOcc(M) ==> <Cons(0, l), T>: dOcc(dApp(M, N))"
  "<l, T>: dOcc(N) ==> <Cons(1, l), T>: dOcc(dApp(M, N))"
apply (simp_all add: dOcc_eqns)
apply (rule Occ_consI2 Occ_consI1 | simp
       | (assumption | rule succI1 succI2)+)+
done

lemmas dTerm_def_subterm_Nil = def_subterm_Nil [OF
  dTerm_Occ_cons_cond dTerm_Occ_ind_cond dOccinv_def
  dSub_def dTerm_Term_cons_inj_cond dsubterm_def]

lemmas dTerm_def_subterm_Cons = def_subterm_Cons [OF
  dTerm_Occ_cons_cond dTerm_Occ_ind_cond dOccinv_def
  dSub_def dTerm_Term_cons_inj_cond dsubterm_def]

lemma dsubterm_eqns_0:
  "[| M: dTerm; l: list(nat) |] ==>
      dsubterm(dLam(M), Cons(0, l)) = dsubterm(M, l)"
  "[| A: dTerm; B: dTerm; l: list(nat) |] ==>
      dsubterm(dApp(A, B), Cons(0, l)) = dsubterm(A, l)"
  "[| A: dTerm; B: dTerm; l: list(nat) |] ==>
      dsubterm(dApp(A, B), Cons(1, l)) = dsubterm(B, l)"
apply (simp_all add: dTerm_cons_eqns_sym dTerm_def_subterm_Cons)
done

lemmas dsubterm_eqns = dTerm_def_subterm_Nil dsubterm_eqns_0

lemma dAbst_eqns:
  "n: nat ==> dAbst(dVar(y), x, n) = if(x = y, dBound(n), dVar(y))"
  "n: nat ==> dAbst(dBound(i), x, n) = dBound(i)"
  "n: nat ==> dAbst(dLam(M), x, n) = dLam(dAbst(M, x, succ(n)))"
  "n: nat ==> dAbst(dApp(A, B), x, n) =
                  dApp(dAbst(A, x, n), dAbst(B, x, n))"
apply (unfold dAbst_def)
apply simp_all
done

lemma dAbst_type:
  assumes major: "M: dTerm"
  and sub: "n: nat"
  shows "dAbst(M, x, n): dTerm"
apply (rule sub [THEN [2] bspec])
apply (rule major [THEN dTerm.induct])
apply (simp_all add: dAbst_eqns)
apply (rule_tac [3] ballI)
apply (drule_tac [3] bspec)
apply (erule_tac [3] nat_succI)
apply blast+
done

lemma dLift_eqns:
  "n: nat ==> dLift(dVar(x), n) = dVar(x)"
  "n: nat ==> dLift(dBound(i), n) = if (i < n, dBound(i), dBound(succ(i)))"
  "n: nat ==> dLift(dLam(M), n) = dLam(dLift(M, succ(n)))"
  "n: nat ==> dLift(dApp(A, B), n) =
                  dApp(dLift(A, n), dLift(B, n))"
apply (unfold dLift_def)
apply simp_all
done

lemma dLift_type:
  assumes major: "M: dTerm"
  and sub: "n: nat"
  shows "dLift(M, n): dTerm"
apply (rule sub [THEN [2] bspec])
apply (rule major [THEN dTerm.induct])
apply (simp_all add: dLift_eqns)
apply (rule_tac [3] ballI)
apply (drule_tac [3] bspec)
apply (erule_tac [3] nat_succI)
apply blast+
done

lemma dSubst_eqns:
  "[| n: nat; N: dTerm |] ==> dSubst(dVar(x), n, N) = dVar(x)"
  "[| n: nat; N: dTerm |] ==> dSubst(dBound(i), n, N) =
              if (n < i, dBound(i #- 1), if (n = i, N, dBound(i)))"
  "[| n: nat; N: dTerm |] ==> dSubst(dLam(M), n, N)
                        = dLam(dSubst(M, succ(n), dLift(N, 0)))"
  "[| n: nat; N: dTerm |] ==> dSubst(dApp(A, B), n, N) =
                  dApp(dSubst(A, n, N), dSubst(B, n, N))"
apply (unfold dSubst_def)
apply simp_all
done

lemma dSubst_type:
  assumes major: "M: dTerm"
  and sub: "n: nat"
  and prem: "N: dTerm"
  shows "dSubst(M, n, N): dTerm"
apply (rule sub [THEN [2] bspec])
apply (rule prem [THEN [2] bspec])
apply (rule major [THEN dTerm.induct])
apply (simp_all add: dSubst_eqns)
apply safe
apply (erule_tac [3] bspec [THEN bspec])
apply (erule_tac [2] bspec [THEN bspec])
apply (erule_tac [1] bspec [THEN bspec])
apply (assumption | rule dLift_type nat_succI nat_0I)+
done

lemma dDeg_eqns:
  "dDeg(dVar(x)) = 0"
  "dDeg(dBound(i)) = succ(i)"
  "dDeg(dLam(M)) = dDeg(M) #- 1"
  "dDeg(dApp(A, B)) = dDeg(A) Un dDeg(B)"
apply (unfold dDeg_def)
apply simp_all
done

lemma dDeg_type:
  "M: dTerm ==> dDeg(M): nat"
apply (unfold dDeg_def)
apply (rule dTerm_rec_type)
apply (assumption | rule diff_type nat_UnI nat_succI nat_0I)+
done


(** dLamDeg **)
lemma dLamDegBase_Nil:
  "M: dTerm ==> dLamDegBase([], M) = 0"
apply (unfold dLamDegBase_def)
apply (rule equalityI)
apply (safe elim!: initseg_NilE)
done

lemma dLamDegBase_Cons_dLam:
  "l: list(nat) ==> dLamDegBase(Cons(0, l), dLam(M))
                 = cons(<[], TdLam>, Occ_shift(0, dLamDegBase(l, M)))"
apply (unfold dLamDegBase_def)
apply (rule equalityI)
apply (safe elim!: list.free_elims Occ_shiftE initseg_ConsE dOcc_dTermEs)
apply (erule swap, rule Occ_shiftI)
apply blast
apply (rule dOcc_dTermIs)
apply (erule_tac [2] dOcc_dTermIs)
apply (erule_tac [2] asm_rl | rule_tac [2] conjI refl exI)+
apply (assumption | rule conjI refl exI)+
apply (blast elim!: list.free_elims)
prefer 2 apply (blast elim!: list.free_elims)
apply (assumption | rule list.intros initseg_NilI initseg_ConsI
         nat_0I)+
done

lemma dLamDegBase_Cons_dApp1:
  "l: list(nat) ==> dLamDegBase(Cons(0, l), dApp(M, N))
                 = Occ_shift(0, dLamDegBase(l, M))"
apply (unfold dLamDegBase_def)
apply (rule equalityI)
apply (safe elim!: list.free_elims dTag.free_elims Occ_shiftE
         initseg_ConsE dOcc_dTermEs)
apply (rule Occ_shiftI)
apply blast
apply (erule dOcc_dTermIs)
apply (assumption | rule conjI refl exI)+
apply (blast elim!: list.free_elims)
apply (assumption | rule list.intros initseg_ConsI nat_0I)+
done

lemma dLamDegBase_Cons_dApp2:
  "l: list(nat) ==> dLamDegBase(Cons(1, l), dApp(M, N))
                 = Occ_shift(1, dLamDegBase(l, N))"
apply (unfold dLamDegBase_def)
apply (rule equalityI)
apply (safe elim!: list.free_elims dTag.free_elims Occ_shiftE
         initseg_ConsE dOcc_dTermEs)
apply (rule Occ_shiftI)
apply blast
apply (erule dOcc_dTermIs)
apply (assumption | rule conjI refl exI)+
apply (blast elim!: list.free_elims)
apply (assumption | rule list.intros initseg_ConsI nat_1I)+
done

lemmas dTerm_Occ_ind_cond_Occ_FinI = Occ_ind_cond_Occ_FinI [OF
  dTerm_Occ_ind_cond]

lemma dLamDeg_type:
  "M: dTerm ==> dLamDeg(l, M): nat"
apply (unfold dLamDeg_def dLamDegBase_def)
apply (assumption | rule Finite_imp_card_nat Fin_into_Finite
         dTerm_Occ_ind_cond_Occ_FinI Collect_subset Fin_subset)+
done

lemma dLamDeg_Nil:
  "M: dTerm ==> dLamDeg([], M) = 0"
apply (unfold dLamDeg_def)
apply (simp only: dLamDegBase_Nil)
apply (rule Card_0 [THEN Card_cardinal_eq])
done

lemma dLamDeg_Cons_dLam:
  assumes major: "M: dTerm"
  and prem: "l: list(nat)"
  shows "dLamDeg(Cons(0, l), dLam(M)) = succ(dLamDeg(l, M))"
apply (unfold dLamDeg_def)
apply (simp only: prem [THEN dLamDegBase_Cons_dLam])
apply (rule trans)
apply (rule Finite_cardinal_cons)
apply (rule_tac [3] f="succ" in function_apply_eq)
apply (rule_tac [3] Occ_shift_cardinal)
apply (unfold dLamDegBase_def)
apply (assumption | rule Fin_into_Finite Occ_shift_FinI
         Collect_subset major nat_0I
         dTerm_Occ_ind_cond_Occ_FinI Fin_subset)+
apply (blast elim!: list.free_elims Occ_shiftE)
apply (rule subset_trans)
apply (assumption | rule major dOcc_domain Collect_subset)+
done

lemma dLamDeg_Cons_dApp1:
  "[| M: dTerm; l: list(nat) |]  ==>
         dLamDeg(Cons(0, l), dApp(M, N)) = dLamDeg(l, M)"
apply (unfold dLamDeg_def)
apply (simp only: dLamDegBase_Cons_dApp1)
apply (rule Occ_shift_cardinal)
apply (unfold dLamDegBase_def)
apply (rule subset_trans)
apply (assumption | rule dOcc_domain Collect_subset)+
done

lemma dLamDeg_Cons_dApp2:
  "[| N: dTerm; l: list(nat) |]  ==>
         dLamDeg(Cons(1, l), dApp(M, N)) = dLamDeg(l, N)"
apply (unfold dLamDeg_def)
apply (simp only: dLamDegBase_Cons_dApp2)
apply (rule Occ_shift_cardinal)
apply (unfold dLamDegBase_def)
apply (rule subset_trans)
apply (assumption | rule dOcc_domain Collect_subset)+
done

lemmas dLamDeg_eqns = dLamDeg_Nil dLamDeg_Cons_dLam dLamDeg_Cons_dApp1
                    dLamDeg_Cons_dApp2


(** dFV **)
lemma dFV_I:
  "[| <l, TdVar(x)>: dOcc(M); M: dTerm |] ==> x: dFV(M)"
apply (unfold dFV_def)
apply (frule dOcc_typeD2)
apply assumption
apply (erule dTag_typeEs)
apply (assumption | rule exI CollectI)+
done

lemma dFV_I2:
  "[| <l, TdVar(x)>: dOcc(M); x: LVariable |] ==> x: dFV(M)"
apply (unfold dFV_def)
apply (assumption | rule exI CollectI)+
done

lemma dFV_E:
  "[| x: dFV(M); !!l. [| x: LVariable; <l, TdVar(x)>: dOcc(M) |] ==> R |]
    ==> R"
apply (unfold dFV_def)
apply blast
done

lemma dFV_Fin:
  "M: dTerm ==> dFV(M): Fin(LVariable)"
apply (unfold dFV_def)
apply (erule dTerm_Occ_ind_cond_Occ_FinI [THEN Fin_induct])
apply simp
apply (erule SigmaE)
apply (erule dTag.cases)
apply safe
apply (rule_tac P="%x. x: Fin(LVariable)" in ssubst)
apply (erule_tac [2] Fin.intros)
prefer 2 apply assumption
apply (rule_tac [2] P="%x. x: Fin(LVariable)" in ssubst)
prefer 3 apply assumption
apply (rule_tac [3] P="%x. x: Fin(LVariable)" in ssubst)
prefer 4 apply assumption
apply (rule_tac [4] P="%x. x: Fin(LVariable)" in ssubst)
prefer 5 apply assumption
apply (rule equalityI, blast elim!: dTag.free_elims,
       blast elim!: dTag.free_elims)+
done

lemma dFV_not_in_lemma:
  "[| x ~: dFV(M); M: dTerm |] ==> ~(EX l. <l, TdVar(x)>: dOcc(M))"
apply (blast intro!: dFV_I)
done

lemma dFV_dVar:
  "x: LVariable ==> dFV(dVar(x)) = {x}"
apply (rule equalityI)
apply (safe elim!: dOcc_dTermEs dFV_E dTag.free_elims)
apply (assumption | rule dFV_I dTerm.intros dOcc_dTermIs)+
done

lemma dFV_dBound:
  "dFV(dBound(x)) = 0"
apply (rule equalityI)
apply (safe elim!: dOcc_dTermEs dFV_E dTag.free_elims)
done

lemma dFV_dLam:
  "M: dTerm ==> dFV(dLam(M)) = dFV(M)"
apply (rule equalityI)
apply (safe elim!: dOcc_dTermEs dFV_E dTag.free_elims)
apply (assumption | rule dFV_I dTerm.intros dOcc_dTermIs)+
done

lemma dFV_dApp:
  "[| M: dTerm; N: dTerm |] ==> dFV(dApp(M, N)) = dFV(M) Un dFV(N)"
apply (rule equalityI)
apply (safe elim!: dOcc_dTermEs dFV_E dTag.free_elims)
apply (erule_tac [2] swap)
apply (assumption | rule dFV_I dTerm.intros
       | erule dOcc_dTermIs)+
done

lemmas dFV_eqns = dFV_dVar dFV_dBound dFV_dApp dFV_dLam

declare nat_ltI [simp del]
lemmas dTerm_ss_simps = nat_succ_Un Un_diff (* dArity_eqns *)
    (* add_0_right add_succ_right *) gt_not_eq lt_asym_if
    le_asym_if not_lt_iff_le lt_irrefl_if
    diff_le_iff lt_diff_iff diff_diff_eq_diff_add
    Un_least_lt_iff [OF nat_into_Ord nat_into_Ord]
    dLift_eqns dSubst_eqns dsubterm_eqns dDeg_eqns
    dAbst_eqns dLamDeg_eqns dFV_eqns
lemmas dTerm_ss_typechecks = dDeg_type dAbst_type
    dSubst_type dLift_type dLamDeg_type dTerm.intros
    nat_UnI

declare dTerm_ss_simps [simp]
declare dTerm_ss_typechecks [TC]
(* declare split_if [split del] *)


(** dProp **)
lemma dPropI:
  "[| M: dTerm; dDeg(M) = 0 |] ==> M: dProp"
apply (unfold dProp_def)
apply blast
done

lemma dPropE:
  "[| M: dProp; [| M: dTerm; dDeg(M) = 0 |] ==> R |] ==> R"
apply (unfold dProp_def)
apply blast
done

lemma dPropD1:
  "M: dProp ==> M: dTerm"
apply (unfold dProp_def)
apply (erule CollectD1)
done

lemma dPropD2:
  "M: dProp ==> dDeg(M) = 0"
apply (unfold dProp_def)
apply (erule CollectD2)
done

lemma dProp_dVarI:
  "x: LVariable ==> dVar(x): dProp"
apply (blast intro: dPropI dDeg_eqns)
done

lemma dProp_dLamI1:
  "M: dProp ==> dLam(M): dProp"
apply (erule dPropE)
apply (rule dPropI)
prefer 2 apply simp
apply (assumption | rule dTerm.intros)+
done

lemma dProp_dLamI2:
  "[| M: dTerm; dDeg(M) = 1 |] ==> dLam(M): dProp"
apply (rule dPropI)
prefer 2 apply simp
apply (assumption | rule dTerm.intros)+
done

lemma dProp_dAppI:
  "[| A: dProp; B: dProp |] ==> dApp(A, B): dProp"
apply (erule dPropE)+
apply (rule dPropI)
prefer 2 apply simp
apply (assumption | rule dTerm.intros)+
done

lemmas dProp_dTermIs = dProp_dVarI dProp_dLamI1 dProp_dLamI2 dProp_dAppI

lemma dProp_dVarE:
  "[| dVar(x): dProp; x: LVariable ==> R |] ==> R"
apply (blast elim!: dPropE dTerm_typeEs)
done

lemma dProp_dBoundE:
  "dBound(n): dProp ==> R"
apply (erule dPropE)
apply (simp only: dDeg_eqns)
apply (erule succ_neq_0)
done

lemma dProp_dLamE:
  assumes major: "dLam(M): dProp"
  and "M: dProp ==> R"
  and "[| M: dTerm; dDeg(M) = 1 |] ==> R"
  shows "R"
apply (rule major [THEN dPropE])
apply (simp only: dDeg_eqns)
apply (erule dTerm_typeEs)
apply (rule dDeg_type [THEN natE])
apply assumption
apply (rotate_tac [2] 1)
prefer 2 apply simp
apply (blast intro: dPropI assms)+
done

lemma dProp_dAppE:
  assumes major: "dApp(A, B): dProp"
  and prem: "[| A: dProp; B: dProp |] ==> R"
  shows "R"
apply (rule major [THEN dPropE])
apply (simp only: dDeg_eqns)
apply (erule dTerm_typeEs)
apply (rule prem)
apply (rule_tac [2] dPropI)
apply (rule dPropI)
prefer 3
apply assumption+
apply (rule_tac [2] equals0I, drule_tac [2] equals0D)
apply (rule_tac [1] equals0I, drule_tac [1] equals0D)
apply (erule notE, erule UnI1)
apply (erule notE, erule UnI2)
done

lemmas dProp_dTermEs = dProp_dVarE dProp_dBoundE dProp_dLamE dProp_dAppE

lemma dProp_induct:
  assumes major: "M: dProp"
  and prem1:
     "!! x. x: LVariable ==> P(dVar(x))"
  and prem2:
     "!! M. [| M: dProp; P(M) |] ==> P(dLam(M))"
  and prem3:
     "!! M. [| M: dTerm; dDeg(M) = 1 |] ==> P(dLam(M))"
  and prem4:
     "!! A B. [| A: dProp; P(A); B: dProp; P(B) |] ==> P(dApp(A, B))"
  shows "P(M)"
apply (rule major [THEN dPropD2, THEN rev_mp])
apply (rule major [THEN dPropD1, THEN dTerm.induct])
prefer 4
apply (rule impI)
apply simp
apply (erule conjE)
prefer 4
apply (rule impI)
apply simp
prefer 4
apply (rule impI)
apply simp
prefer 3
apply (rule impI)
apply simp
apply (erule prem1)
apply (drule diff_eq_0D)
apply (assumption | rule dDeg_type nat_1I)+
apply (drule le_succ_iff [THEN iffD1])
apply (erule disjE)
apply (drule le0_iff [THEN iffD1])
apply (rule_tac [3] prem4)
apply (rule_tac [2] prem3)
apply (rule prem2)
apply (safe intro!: dPropI)
done


(** dBoundBy **)
lemma dBoundByI:
  "[| M: dTerm; <m, TdBound(n)>: dOcc(M); <l, TdLam>: dOcc(M);
      m = l @ x; dLamDeg(x, dsubterm(M, l)) = succ(n)
   |] ==> dBoundBy(<m, TdBound(n)>, <l, TdLam>, M)"
apply (unfold dBoundBy_def)
apply blast
done

lemma dBoundByE:
  assumes major: "dBoundBy(u, v, M)"
  and prem:
     "!! l n x. [| u = <l @ x, TdBound(n)>; v = <l, TdLam>;
        M: dTerm; l: list(nat); x: list(nat);
        <l @ x, TdBound(n)>: dOcc(M); <l, TdLam>: dOcc(M);
        dLamDeg(x, dsubterm(M, l)) = succ(n)
      |] ==> R"
  shows "R"
apply (rule major [unfolded dBoundBy_def, THEN conjE])
apply (erule conjE exE)+
apply (rule prem)
apply safe
apply (assumption | rule refl)+
apply (drule_tac [2] dOcc_typeD1, erule_tac [3] app_typeD)
apply (assumption | rule refl | erule dOcc_typeD1)+
done

lemma dBoundByD1:
  "dBoundBy(u, v, M) ==> M: dTerm"
apply (unfold dBoundBy_def)
apply (erule conjunct1)
done

lemma dBoundBy_dLamI1:
  "[| M: dTerm; dLamDeg(m, M) = n; <m, TdBound(n)>: dOcc(M) |]  ==>
    dBoundBy(<Cons(0, m), TdBound(n)>, <[], TdLam>, dLam(M))"
apply (rule dBoundByI)
apply (rule_tac [4] app_Nil [THEN sym])
apply (drule_tac [4] dOcc_typeD1)
prefer 5 apply simp
apply (assumption | rule nat_succI nat_0I dOcc_dTermIs
         dTerm.intros list.intros)+
done

lemma dBoundBy_dLamI2:
  "dBoundBy(<m, T>, <l, U>, M) ==>
    dBoundBy(<Cons(0, m), T>, <Cons(0, l), U>, dLam(M))"
apply (erule dBoundByE)
apply safe
apply (rule dBoundByI)
apply (rule_tac [4] app_Cons [THEN sym])
prefer 4 apply simp
apply (assumption | rule nat_succI nat_0I initseg_ConsI
         dOcc_dTermIs dTerm.intros)+
done

lemma dBoundBy_dAppI1:
  "[| dBoundBy(<m, T>, <l, U>, A); B: dTerm |] ==>
    dBoundBy(<Cons(0, m), T>, <Cons(0, l), U>, dApp(A, B))"
apply (erule dBoundByE)
apply safe
apply (rule dBoundByI)
apply (rule_tac [4] app_Cons [THEN sym])
prefer 4 apply simp
apply (assumption | rule nat_succI nat_0I initseg_ConsI
         dOcc_dTermIs dTerm.intros)+
done

lemma dBoundBy_dAppI2:
  "[| dBoundBy(<m, T>, <l, U>, B); A: dTerm |] ==>
    dBoundBy(<Cons(1, m), T>, <Cons(1, l), U>, dApp(A, B))"
apply (erule dBoundByE)
apply safe
apply (rule dBoundByI)
apply (rule_tac [4] app_Cons [THEN sym])
prefer 4 apply simp
apply (assumption | rule nat_succI nat_0I initseg_ConsI
         dOcc_dTermIs dTerm.intros)+
done

lemmas dBoundBy_dTermIs = dBoundBy_dLamI1 dBoundBy_dLamI2
                          dBoundBy_dAppI1 dBoundBy_dAppI2

lemma dBoundBy_dBoundE:
  "dBoundBy(u, v, dBound(n)) ==> R"
apply (erule dBoundByE)
apply (erule dOcc_dTermEs)+
apply (blast elim!: dTag.free_elims)
done

lemma dBoundBy_dVarE:
  "dBoundBy(u, v, dVar(x)) ==> R"
apply (erule dBoundByE)
apply (erule dOcc_dTermEs)+
apply (blast elim!: dTag.free_elims)
done

lemma dBoundBy_dLamE:
  assumes major: "dBoundBy(u, v, dLam(M))"
  and prem1:
     "!! m. [| u = <Cons(0, m), TdBound(dLamDeg(m, M))>; v = <[], TdLam>;
         M: dTerm; <m, TdBound(dLamDeg(m, M))>: dOcc(M)
      |] ==> R"
  and prem2:
     "!! l m n. [| u = <Cons(0, m), TdBound(n)>; v = <Cons(0, l), TdLam>;
         dBoundBy(<m, TdBound(n)>,  <l, TdLam>, M)
      |] ==> R"
  shows "R"
apply (rule major [THEN dBoundByE])
apply (erule dTerm_typeEs)
apply (rotate_tac 7)
apply (erule dOcc_dTermEs)
apply (erule_tac [2] dOcc_dTermEs)
apply (rule_tac [3] prem2)
apply (rule_tac [2] prem1)
apply (safe elim!: dTag.free_elims dTerm_typeEs list.free_elims)
apply (rotate_tac [1] 3)
apply (rotate_tac [2] 3)
apply (rotate_tac [3] 3)
apply simp_all
apply hypsubst
prefer 2 apply hypsubst
prefer 3 apply hypsubst
apply (assumption | rule refl dBoundByI conjI)+
done

lemma dBoundBy_dAppE:
  assumes major:  "dBoundBy(u, v, dApp(A, B))"
  and prem1:
     "!! l m n. [| u = <Cons(0, m), TdBound(n)>; v = <Cons(0, l), TdLam>;
         dBoundBy(<m, TdBound(n)>,  <l, TdLam>, A); B: dTerm
      |] ==> R"
  and prem2:
     "!! l m n. [| u = <Cons(1, m), TdBound(n)>; v = <Cons(1, l), TdLam>;
         dBoundBy(<m, TdBound(n)>,  <l, TdLam>, B); A: dTerm
      |] ==> R"
  shows "R"
apply (rule major [THEN dBoundByE])
apply (erule dTerm_typeEs)
apply (erule dOcc_dTermEs)
apply (erule_tac [3] dOcc_dTermEs)
apply (erule_tac [2] dOcc_dTermEs)
apply (rule_tac [7] prem2)
apply (rule_tac [3] prem1)
apply (safe elim!: ConsE dTag.free_elims dOcc_dTermEs
         dTerm_typeEs list.free_elims)
apply (simp_all only: app_Nil app_Cons)
apply (safe elim!: list.free_elims)
apply (rotate_tac [2] 2)
apply (rotate_tac [1] 2)
apply simp_all
apply (assumption | rule dBoundByI refl)+
done

lemmas dBoundBy_dTermEs = dBoundBy_dVarE dBoundBy_dBoundE
                          dBoundBy_dLamE dBoundBy_dAppE


(** Some Lemmas **)
lemma dDeg_dAbst_lemma1:
  assumes major: "M: dTerm"
  and prem1: "x ~: dFV(M)"
  and prem2: "n: nat"
  shows "dAbst(M, x, n) = M"
apply (rule prem1 [THEN rev_mp])
apply (rule prem2 [THEN [2] bspec])
apply (rule major [THEN dTerm.induct])
apply simp_all
done

lemma dDeg_dAbst_lemma2:
  assumes major: "M: dTerm"
  and prem1: "x: dFV(M)"
  and prem2: "n: nat"
  shows "dDeg(dAbst(M, x, n)) = succ(n) Un dDeg(M)"
apply (rule prem1 [THEN rev_mp])
apply (rule prem2 [THEN [2] bspec])
apply (rule major [THEN dTerm.induct])
apply (safe elim!: dProp_dTermEs dOcc_dTermEs dTag.free_elims)
apply simp_all
apply (erule disjE)
apply (case_tac [2] "x: dFV(M)")
apply (case_tac [1] "x: dFV(N)")
apply (simp_all add: dDeg_dAbst_lemma1)
apply blast+
done

lemma dDeg_dLift_lemma1:
  assumes major: "dDeg(M) le n"
  and prem1: "M: dTerm"
  and prem2: "n: nat"
  shows "dLift(M, n) = M"
apply (rule major [THEN rev_mp])
apply (rule prem2 [THEN [2] bspec])
apply (rule prem1 [THEN dTerm.induct])
apply simp_all
done

lemma dDeg_dLift_lemma2:
  assumes major: "n < dDeg(M)"
  and prem1: "M: dTerm"
  and prem2: "n: nat"
  shows "dDeg(dLift(M, n)) = succ(dDeg(M))"
apply (rule major [THEN rev_mp])
apply (rule prem2 [THEN [2] bspec])
apply (rule prem1 [THEN dTerm.induct])
apply safe
apply simp_all
apply (rule dDeg_type [THEN natE])
apply assumption
apply (rotate_tac [2] 4)
apply (rotate_tac [1] 4)
apply simp_all
apply (rule_tac i="dDeg(N)" and j="dDeg(M)" in Ord_linear_lt)
apply (rule_tac [5] i="x" and j="dDeg(M)" in Ord_linear2)
apply (rule_tac [3] i="x" and j="dDeg(N)" in Ord_linear2)
prefer 8
prefer 9
apply (assumption | rule nat_into_Ord dDeg_type)+
apply (simp_all add: dDeg_dLift_lemma1 lt_Un_eq_lemma
         trans [OF Un_commute lt_Un_eq_lemma])
apply (rule_tac [2] lt_Un_eq_lemma)
apply (erule_tac [2] leI)
apply (rule trans [OF Un_commute lt_Un_eq_lemma])
apply (erule leI)
done

lemma dDeg_dSubst_lemma1:
  assumes major: "M: dTerm"
  and prem1: "dDeg(M) le n"
  and prem2: "n: nat"
  and prem3: "N: dTerm"
  shows "dSubst(M, n, N) = M"
apply (rule prem1 [THEN rev_mp])
apply (rule prem2 [THEN [2] bspec])
apply (rule prem3 [THEN [2] bspec])
apply (rule major [THEN dTerm.induct])
apply safe
apply simp_all
done

lemma dDeg_dSubst_lemma2:
  assumes major: "M: dTerm"
  and prem1: "n < dDeg(M)"
  and prem2: "n: nat"
  and prem3: "N: dTerm"
  shows "dDeg(dSubst(M, n, N)) le (dDeg(M) #- 1) Un dDeg(N)"
apply (rule prem1 [THEN rev_mp])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem2 [THEN [2] bspec])
apply (rule major [THEN dTerm.induct])
apply safe
apply (case_tac [2] "x = n")
apply (simp_all split del: split_if)
apply (rule Un_upper2_le)
apply (assumption | rule nat_into_Ord dDeg_type)+
apply (subgoal_tac "x < n")
apply (erule_tac [2] swap, rule_tac [2] le_anti_sym)
apply (simp_all add: not_lt_imp_le
            [OF asm_rl nat_into_Ord nat_into_Ord]
            split del: split_if)
apply (rule_tac lt_trans2)
apply (rule_tac [2] Un_upper1_le)
apply (rule gt_pred)
apply (assumption | rule le_refl nat_into_Ord dDeg_type)+

apply (rule_tac M1="M" in dDeg_type [THEN natE])
apply assumption
apply (rotate_tac [1] 5)
apply (rotate_tac [2] 5)
apply (rule_tac [3] i="dDeg(M)" and j="dDeg(N)" in Ord_linear_lt)
apply (erule_tac [3] asm_rl | rule_tac [3] nat_into_Ord dDeg_type)+
apply (frule_tac [5] c="dDeg(M)" in trans [OF Un_commute lt_Un_eq_lemma])
apply (frule_tac [3] B="dDeg(N)" in lt_Un_eq_lemma)
apply (rotate_tac [3] 8)
apply (rotate_tac [4] 7)
apply (rotate_tac [5] 8)
apply simp_all
apply (rule nat_succ_Un [THEN subst])
apply (rule_tac [3] succ_pred [THEN mp, THEN ssubst])
prefer 5 apply assumption
apply (assumption | rule diff_type nat_succI nat_0I dDeg_type)+

apply (rule_tac i="0" and j="dDeg(dSubst(M, succ(x), dLift(xa, 0)))"
        in Ord_linear2)
apply (assumption | rule nat_into_Ord nat_0I nat_succI dDeg_type
        dSubst_type dLift_type)+
prefer 2
apply simp
apply (rule lt_imp_0_lt)
apply (erule Un_upper1_lt)
apply (assumption | rule nat_into_Ord dDeg_type nat_succI)+
apply (rule gt_pred)
prefer 2 apply assumption
apply (drule_tac x2="succ(x)" and x="dLift(xa, 0)" in bspec [THEN mp, THEN bspec])
prefer 4
apply (erule le_trans)
apply (rule_tac M1="xa" in dDeg_type [THEN natE])
apply assumption
apply (simp add: dDeg_dLift_lemma1)
apply (rule Un_upper1_le)
prefer 3
apply (rule dDeg_dLift_lemma2 [THEN ssubst])
apply simp
apply (assumption | rule nat_succI nat_into_Ord dDeg_type
        nat_0I dLift_type le_refl nat_UnI succ_leI dSubst_type)+

apply (rule_tac [2] i="x" and j="dDeg(N)" in Ord_linear2)
apply (rule_tac [1] i="x" and j="dDeg(M)" in Ord_linear2)
prefer 5
prefer 6
apply (assumption | rule nat_into_Ord dDeg_type)+
apply (simp_all add: dDeg_dSubst_lemma1)
apply (drule_tac [1] x="xa" in bspec [THEN mp, THEN bspec],
       erule_tac [1] asm_rl, erule_tac [1] asm_rl,
       erule_tac [1] asm_rl)+
apply (drule_tac [2] x="xa" in bspec [THEN mp, THEN bspec],
       erule_tac [2] asm_rl, erule_tac [2] asm_rl,
       erule_tac [2] asm_rl)+
apply (drule_tac [3] x="xa" in bspec [THEN mp, THEN bspec],
       erule_tac [3] asm_rl, erule_tac [3] asm_rl,
       erule_tac [3] asm_rl)+
apply (drule_tac [4] x="xa" in bspec [THEN mp, THEN bspec],
       erule_tac [4] asm_rl, erule_tac [4] asm_rl,
       erule_tac [4] asm_rl)+
apply safe
prefer 8 apply (erule le_trans)
prefer 8 apply (erule le_trans)
prefer 8 apply (erule le_trans)
prefer 8 apply (erule le_trans)
prefer 8 apply (erule le_trans)
prefer 8 apply (erule le_trans)
prefer 8 apply (erule le_trans)
prefer 8 apply (erule le_trans)
apply simp_all
prefer 4
prefer 5
prefer 6
prefer 7
apply (rule conjI)
apply (rule_tac [2] Un_upper2_le)
apply (rule Un_upper1_le [THEN le_trans])
apply (rule_tac [3] Un_upper1_le)
apply (assumption | rule nat_into_Ord dDeg_type diff_type
         nat_0I nat_succI nat_UnI)+

apply (rule conjI)
apply (rule_tac [2] Un_upper2_le)
apply (rule Un_upper2_le [THEN le_trans])
apply (rule_tac [3] Un_upper1_le)
apply (assumption | rule nat_into_Ord dDeg_type diff_type
         nat_0I nat_succI nat_UnI)+

apply (rule conjI)
apply (rule_tac [2] Un_upper2_le)
apply (rule Un_upper1_le [THEN le_trans])
apply (rule_tac [3] Un_upper1_le)
apply (assumption | rule nat_into_Ord dDeg_type diff_type
         nat_0I nat_succI nat_UnI)+

apply (rule conjI)
apply (rule_tac [2] Un_upper2_le)
apply (rule Un_upper2_le [THEN le_trans])
apply (rule_tac [3] Un_upper1_le)
apply (assumption | rule nat_into_Ord dDeg_type diff_type
         nat_0I nat_succI nat_UnI)+

apply (rule conjI)
apply (rule_tac [2] Un_upper2_le)
apply (rule Un_upper1_le [THEN le_trans])
apply (rule_tac [3] Un_upper1_le)
apply (assumption | rule nat_into_Ord dDeg_type diff_type
         nat_0I nat_succI nat_UnI)+

apply (rule conjI)
apply (rule_tac [2] Un_upper2_le)
apply (rule Un_upper2_le [THEN le_trans])
apply (rule_tac [3] Un_upper1_le)
apply (assumption | rule nat_into_Ord dDeg_type diff_type
         nat_0I nat_succI nat_UnI)+

apply (rule_tac j="dDeg(N) #- 1" in le_trans)
apply (erule lt_imp_le_pred)
prefer 2
apply (rule Un_upper2_le [THEN le_trans])
apply (rule_tac [3] Un_upper1_le)
apply (assumption | rule nat_into_Ord dDeg_type diff_type
         nat_0I nat_succI nat_UnI)+

apply (rule_tac j="dDeg(M) #- 1" in le_trans)
apply (erule lt_imp_le_pred)
prefer 2
apply (rule Un_upper1_le [THEN le_trans])
apply (rule_tac [3] Un_upper1_le)
apply (assumption | rule nat_into_Ord dDeg_type diff_type
         nat_0I nat_succI nat_UnI)+

done

lemma dDeg_dSubst_lemma3:
  assumes prem1: "M: dTerm"
  and prem2: "dDeg(M) = 1"
  and prem3: "N: dProp"
  shows "dSubst(M, 0, N): dProp"
apply (insert prem1 prem2 prem3 [THEN dPropD1] prem3 [THEN dPropD2])
apply (rule_tac M1="M" and n1="0" and N1="N" in
         dDeg_dSubst_lemma2 [THEN revcut_rl])
apply (rule_tac [2] prem2 [THEN ssubst])
apply (assumption | rule le_refl nat_0I nat_into_Ord)+
apply simp
apply (assumption | rule dPropI dSubst_type nat_0I)+
done

lemma dSubst_dAbst_lemma:
  assumes prem1: "M: dTerm"
  and prem2: "x: LVariable"
  and prem3: "n: nat"
  and prem4: "dDeg(M) le n"
  shows "dSubst(dAbst(M, x, n), n, dVar(x)) = M"
apply (insert prem2)
apply (rule prem4 [THEN rev_mp])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem1 [THEN dTerm.induct])
apply safe
apply (case_tac "x = xa")
apply simp_all
done

lemma dSubst_dAbst_lemma2:
  assumes major: "M: dProp"
  and prem: "x: LVariable"
  shows "dSubst(dAbst(M, x, 0), 0, dVar(x)) = M"
apply (rule dSubst_dAbst_lemma)
apply (rule_tac [4] major [THEN dPropD2, THEN ssubst])
apply (assumption | rule major [THEN dPropD1] prem nat_0I
         Ord_0 le_refl)+
done

lemma dSubst_dAbst_lemma3:
  assumes prem1: "dDeg(M) le n"
  and prem2: "M: dTerm"
  and prem3: "N: dTerm"
  and prem4: "n: nat"
  shows "dSubst(dAbst(M, x, succ(n)), succ(n), N) =
              dSubst(dAbst(M, x, n), n, N)"
apply (rule prem1 [THEN rev_mp])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem4 [THEN [2] bspec])
apply (rule prem2 [THEN dTerm.induct])
apply (rule_tac [2] ballI)
apply (case_tac [2] "xa = n")
apply (case_tac "x = xa")
apply simp_all
apply safe
apply (subgoal_tac "succ(x) ~= n" "~ succ(x) < n")
apply simp
apply safe
apply (drule_tac [2] leI [THEN succ_le_iff [THEN iffD1]])
apply (erule_tac [2] lt_irrefl)
apply (drule lt_trans, assumption)
apply (drule leI [THEN succ_le_iff [THEN iffD1]],
       erule lt_irrefl)
done

lemma dAbst_dSubst_lemma:
  assumes prem1: "M: dTerm"
  and prem2: "x: LVariable"
  and prem3: "x ~: dFV(M)"
  and prem4: "n: nat"
  and prem5: "dDeg(M) le succ(n)"
  shows "dAbst(dSubst(M, n, dVar(x)), x, n) = M"
apply (insert prem2)
apply (rule prem3 [THEN rev_mp])
apply (rule prem5 [THEN rev_mp])
apply (rule prem4 [THEN [2] bspec])
apply (rule prem1 [THEN dTerm.induct])
apply safe
apply (case_tac [2] "xa = n")
apply (case_tac [3] "xa < n")
apply simp_all
apply (drule lt_trans2, assumption)
apply (erule lt_irrefl)
done

lemma dAbst_dLift_lemma:
  assumes prem1: "m le n"
  and prem2: "M: dTerm"
  and prem3: "n: nat"
  and prem4: "m: nat"
  shows "dAbst(dLift(M, m), x, succ(n))
            = dLift(dAbst(M, x, n), m)"
apply (rule prem1 [THEN rev_mp])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem4 [THEN [2] bspec])
apply (rule prem2 [THEN dTerm.induct])
apply safe
apply (case_tac [2] "xa = n")
apply (case_tac [3] "n < xa")
apply (case_tac [1] "x = xa")
apply simp_all
done

lemma dAbst_dSubst_lemma2:
  assumes prem1: "m le n"
  and prem3: "M: dTerm"
  and prem4: "N: dTerm"
  and prem5: "n: nat"
  and prem6: "m: nat"
  shows "dAbst(dSubst(M, m, N), x, n)
            = dSubst(dAbst(M, x, succ(n)), m, dAbst(N, x, n))"
apply (rule prem1 [THEN rev_mp])
apply (rule prem4 [THEN [2] bspec])
apply (rule prem5 [THEN [2] bspec])
apply (rule prem6 [THEN [2] bspec])
apply (rule prem3 [THEN dTerm.induct])
apply safe
apply (case_tac [2] "xa = n")
apply (case_tac [3] "xa < n")
apply (case_tac "x = xa")
apply (simp_all add: dAbst_dLift_lemma)
done

lemma dLift_dLift_lemma:
  assumes prem1: "m le n"
  and prem2: "M: dTerm"
  and prem4: "n: nat"
  and prem5: "m: nat"
  shows "dLift(dLift(M, m), succ(n)) = dLift(dLift(M, n), m)"
apply (rule prem1 [THEN rev_mp])
apply (rule prem4 [THEN [2] bspec])
apply (rule prem5 [THEN [2] bspec])
apply (rule prem2 [THEN dTerm.induct])
apply simp_all
apply safe
apply (frule le_anti_sym, assumption)
apply hypsubst
apply assumption
apply (erule lt_trans, assumption)
apply (erule lt_trans1, assumption)
apply (erule lt_trans, assumption)
done

lemma dLift_dSubst_lemma:
  assumes prem1: "m le n"
  and prem2: "M: dTerm"
  and prem3: "N: dTerm"
  and prem4: "n: nat"
  and prem5: "m: nat"
  shows "dLift(dSubst(M, n, N), m) = dSubst(dLift(M, m), succ(n),
                                        dLift(N, m))"
apply (rule prem1 [THEN rev_mp])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem4 [THEN [2] bspec])
apply (rule prem5 [THEN [2] bspec])
apply (rule prem2 [THEN dTerm.induct])
apply (simp_all add: dLift_dLift_lemma)
apply safe
apply (drule_tac i="n" in lt_trans2, assumption)
apply (erule lt_irrefl)
apply (drule_tac i="succ(xa)" in lt_trans2, assumption)
apply simp
apply (drule_tac i="n" in lt_trans2, assumption)
apply (drule_tac i="xa" and j="n" and k="xa" in lt_trans, assumption)
apply (erule lt_irrefl)
apply (drule_tac i="succ(xa)" in lt_trans2, assumption)
apply simp
apply (drule_tac i="x" and k="n" in lt_trans1, assumption)
apply (erule_tac n="n" in natE)
apply hypsubst
apply (erule lt0E)
apply hypsubst
apply simp
apply (drule_tac i="xb" and k="xb" in lt_trans2, assumption)
apply (erule lt_irrefl)
apply (drule_tac i="n" and k="n" in lt_trans2, assumption)
apply (erule lt_irrefl)
apply (drule_tac i="succ(xa)" and k="xa" in lt_trans2, assumption)
apply simp
apply (drule_tac i="n" and k="xa" in lt_trans2, assumption)
apply (drule_tac i="n" and k="n" in lt_trans, assumption)
apply (erule lt_irrefl)
apply (drule_tac i="n" and k="xa" in lt_trans2, assumption)
apply (drule_tac i="n" and k="n" in lt_trans, assumption)
apply (erule lt_irrefl)
apply (drule_tac i="n" and k="n #- 1" in lt_trans2, assumption)
apply simp
apply (erule_tac n="n" in natE)
apply hypsubst
apply simp
apply hypsubst
apply simp
done

lemma dSubst_dSubst_lemma1:
  assumes prema: "dDeg(M) le succ(m)"
  and prem0: "dDeg(A) = 0"
  and prem1: "m le n"
  and prem2: "M: dTerm"
  and prem3: "A: dTerm"
  and prem4: "B: dTerm"
  and prem5: "n: nat"
  and prem6: "m: nat"
  shows "dSubst(dSubst(M, m, A), n, B) =
              dSubst(dSubst(M, succ(n), dLift(B, 0)), m, A)"
apply (rule prema [THEN rev_mp])
apply (rule prem0 [THEN rev_mp])
apply (rule prem1 [THEN rev_mp])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem4 [THEN [2] bspec])
apply (rule prem5 [THEN [2] bspec])
apply (rule prem6 [THEN [2] bspec])
apply (rule prem2 [THEN dTerm.induct])
apply (simp_all add: dDeg_dLift_lemma1 split del: split_if)
apply safe
apply (case_tac "x = n")
apply (subgoal_tac [2] "n < x" "n < xa")
apply (erule_tac [4] swap, rule_tac [4] le_anti_sym)
apply (erule_tac [3] lt_trans2, erule_tac [3] asm_rl)
apply hypsubst
apply (simp_all split del: split_if add: leI dDeg_dSubst_lemma1)
done

lemma dSubst_dSubst_lemma2:
  assumes prem0: "dDeg(B) = 0"
  and prem1: "m le n"
  and prem2: "M: dTerm"
  and prem3: "A: dTerm"
  and prem4: "B: dTerm"
  and prem5: "n: nat"
  and prem6: "m: nat"
  shows "dSubst(dSubst(M, m, A), n, B) =
              dSubst(dSubst(M, succ(n), B), m, dSubst(A, n, B))"
apply (rule prem0 [THEN rev_mp])
apply (rule prem1 [THEN rev_mp])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem4 [THEN [2] bspec])
apply (rule prem5 [THEN [2] bspec])
apply (rule prem6 [THEN [2] bspec])
apply (rule prem2 [THEN dTerm.induct])
apply (simp_all split del: split_if
         add: dDeg_dLift_lemma1 dLift_dSubst_lemma)
apply safe
apply (rule_tac i="n" and j="x" in Ord_linear_lt)
apply (assumption | rule nat_into_Ord)+
apply (subgoal_tac "n < xa")
apply (erule_tac [2] lt_trans2, erule_tac [2] asm_rl)
apply (rule_tac [3] i="n" and j="succ(xa)" in Ord_linear_lt)
apply (erule_tac [3] asm_rl | rule_tac [3] nat_into_Ord nat_succI)+
apply (subgoal_tac [5] "succ(x) < n")
apply (subgoal_tac [3] "xa ~= n #- 1")
apply (simp_all split del: split_if
        add: leI dDeg_dSubst_lemma1 not_lt_iff_le [OF nat_into_Ord nat_into_Ord])
apply (rule_tac [2] j="succ(xa)" in lt_trans1)
prefer 3 apply assumption
apply (erule_tac n="n" in natE)
apply safe
apply simp
apply (erule lt_irrefl)
done

lemma dFV_dAbst:
  assumes major: "M: dTerm"
  and prem: "n:nat"
  shows "dFV(dAbst(M, x, n)) = dFV(M) - {x}"
apply (rule prem [THEN rev_bspec])
apply (rule major [THEN dTerm.induct])
apply (case_tac "x = xa")
apply simp_all
apply blast+
done

lemma dDeg_dLamDeg_lemma1:
  assumes prem1: "M: dTerm"
  and prem2: "<l, TdBound(n)>: dOcc(M)"
  shows "n < dDeg(M) #+ dLamDeg(l, M)"
apply (rule prem2 [THEN rev_mp])
apply (rule_tac x="l" in spec)
apply (rule prem1 [THEN dTerm.induct])
apply (safe elim!: dOcc_dTermEs dTag.free_elims)
apply (frule_tac [4] dOcc_typeD1, erule_tac [4] asm_rl)
apply (frule_tac [3] dOcc_typeD1, erule_tac [3] asm_rl)
apply (frule_tac [2] dOcc_typeD1, erule_tac [2] asm_rl)
apply (simp_all split del: split_if)
apply (rule dDeg_type [THEN natE])
apply assumption
apply (rotate_tac [1] 4)
apply (rotate_tac [2] 4)
apply simp
prefer 2
apply simp
apply (drule_tac [3] spec [THEN mp], erule_tac [3] asm_rl)
apply (drule_tac [2] spec [THEN mp], erule_tac [2] asm_rl)
apply (drule_tac [1] spec [THEN mp], erule_tac [1] asm_rl)
apply (erule leI)
apply (erule_tac [2] lt_trans2)
apply (rule_tac [2] add_le_mono1)
apply (erule_tac [1] lt_trans2)
apply (rule_tac [1] add_le_mono1)
apply (assumption | rule dLamDeg_type dDeg_type nat_UnI
         Un_upper1_le Un_upper2_le nat_into_Ord)+
done

lemma dDeg_0_lemma:
  assumes prem1: "M: dTerm"
  and prem2: "~(EX l n. <l, TdBound(n)>: dOcc(M))"
  shows "dDeg(M) = 0"
apply (rule prem2 [THEN rev_mp])
apply (rule prem1 [THEN dTerm.induct])
apply (simp_all split del: split_if)
apply (assumption | rule exI dOcc_dTermIs)+
apply (safe elim!: dOcc_dTermEs dTag.free_elims)
prefer 2 apply simp
prefer 5 apply simp
apply (blast intro: dOcc_dTermIs)+
done

lemma dDeg_dLamDeg_lemma2:
  assumes prem1: "M: dTerm"
  and prem2: "EX l n. <l, TdBound(n)>: dOcc(M)"
  shows "EX l n. <l, TdBound(n)>: dOcc(M) &
               dDeg(M) = succ(n) #- dLamDeg(l, M)"
apply (rule prem2 [THEN rev_mp])
apply (rule prem1 [THEN dTerm.induct])
apply (safe elim!: dOcc_dTermEs dTag.free_elims)
prefer 2 apply (erule swap, rule exI [THEN exI], assumption)
prefer 3 apply (erule swap, rule exI [THEN exI], assumption)
prefer 3 apply (erule swap, rule exI [THEN exI], assumption)
prefer 3 apply (erule swap, rule exI [THEN exI], assumption)
prefer 5 apply (erule swap, rule exI [THEN exI], assumption)
apply (rule exI [THEN exI])
apply (rule conjI)
apply (rule dOcc_dTermIs)
apply simp
apply (rule_tac x="Cons(0, lb)" in exI)
apply (frule_tac l="lb" in dOcc_typeD1, assumption)
apply (frule_tac T="TdBound(na)" in dOcc_typeD2, assumption)
apply (erule dTag_typeEs)
apply (rule_tac [2] x="Cons(1, la)" in exI)
apply (frule_tac [2] l="la" in dOcc_typeD1, erule_tac [2] asm_rl)
apply (rule_tac [3] x="Cons(0, la)" in exI)
apply (frule_tac [3] l="la" in dOcc_typeD1, erule_tac [3] asm_rl)
apply (rule_tac [5] i="dDeg(M)" and j="dDeg(N)" in Ord_linear2)
apply (erule_tac [5] asm_rl | rule_tac [5] nat_into_Ord dDeg_type)+
apply (rule_tac [4] i="dDeg(M)" and j="dDeg(N)" in Ord_linear2)
apply (erule_tac [4] asm_rl | rule_tac [4] nat_into_Ord dDeg_type)+
apply (rule_tac [4] x="Cons(1, lb)" in exI)
apply (frule_tac [4] l="lb" in dOcc_typeD1, erule_tac [4] asm_rl)
apply (rule_tac [5] x="Cons(0, la)" in exI)
apply (frule_tac [5] l="la" in dOcc_typeD1, erule_tac [5] asm_rl)
apply (rule_tac [6] x="Cons(1, lb)" in exI)
apply (frule_tac [6] l="lb" in dOcc_typeD1, erule_tac [6] asm_rl)
apply (rule_tac [7] x="Cons(0, la)" in exI)
apply (frule_tac [7] l="la" in dOcc_typeD1, erule_tac [7] asm_rl)
apply (rule_tac [1] exI, rule_tac [1] conjI, erule_tac [1] dOcc_dTermIs)
apply (rule_tac [2] exI, rule_tac [2] conjI, erule_tac [2] dOcc_dTermIs)
apply (rule_tac [3] exI, rule_tac [3] conjI, erule_tac [3] dOcc_dTermIs)
apply (rule_tac [4] exI, rule_tac [4] conjI, erule_tac [4] dOcc_dTermIs)
apply (rule_tac [5] exI, rule_tac [5] conjI, erule_tac [5] dOcc_dTermIs)
apply (rule_tac [6] exI, rule_tac [6] conjI, erule_tac [6] dOcc_dTermIs)
apply (rule_tac [7] exI, rule_tac [7] conjI, erule_tac [7] dOcc_dTermIs)
apply (simp_all add: dDeg_0_lemma le_Un_eq_lemma lt_Un_eq_lemma del: not_ex)
apply (rule_tac [1] Un_commute [THEN subst])
apply (rule_tac [2] Un_commute [THEN subst])
apply (simp_all add: le_Un_eq_lemma)
done

lemma dBoundBy_dLamDeg_lemma1:
  assumes major: "dBoundBy(<l, TdBound(n)>, v, M)"
  shows "succ(n) #- dLamDeg(l, M) = 0"
apply (rule major [THEN rev_mp])
apply (rule_tac x="v" in spec)
apply (rule_tac x="l" and A="list(nat)" in bspec)
apply (rule_tac x="n" and A="nat" in bspec)
apply (rule_tac [2] major [THEN dBoundByE])
apply (rule_tac [3] major [THEN dBoundByE])
apply (rule major [THEN dBoundByD1, THEN dTerm.induct])
apply (safe elim!: dBoundBy_dTermEs dTag.free_elims ConsE)
apply (erule_tac [6] asm_rl | rule_tac [6] app_type)+
apply (drule_tac [5] dOcc_typeD2)
apply (erule_tac [6] dTag_typeEs)
apply (erule_tac [5] asm_rl)+
apply (simp_all del: all_simps) 
apply (drule bspec [THEN bspec, THEN spec, THEN mp])
prefer 3 apply assumption
prefer 3
apply (simp only: le0_iff [THEN iff_sym])
apply (rule le_trans)
prefer 2 apply assumption
apply (assumption | rule diff_le_mono1 dLamDeg_type le_refl
         nat_into_Ord nat_succI leI)+
done

lemma dBoundBy_dLamDeg_lemma2:
  assumes major: "M: dTerm"
  and prem1: "<l, TdBound(n)>: dOcc(M)"
  and prem2: "n < dLamDeg(l, M)"
  shows "EX m. dBoundBy(<l, TdBound(n)>, <m, TdLam>, M)"
apply (rule prem1 [THEN rev_mp])
apply (rule prem2 [THEN rev_mp])
apply (rule_tac x="l" and A="list(nat)" in bspec)
apply (rule_tac x="n" and A="nat" in bspec)
apply (rule_tac [2] dOcc_typeD2 [OF prem1 major, THEN revcut_rl])
apply (rule_tac [3] dOcc_typeD1 [OF prem1 major])
apply (rule major [THEN dTerm.induct])
apply (safe elim!: dTag_typeEs dOcc_dTermEs ConsE dTag.free_elims)
apply (rotate_tac [2] 4)
apply (rotate_tac [3] 6)
apply (rotate_tac [4] 6)
apply simp_all
apply (erule leE)
prefer 2
apply hypsubst
apply (rule exI)
apply (assumption | rule refl dBoundBy_dLamI1)+
apply (drule_tac [3] bspec [THEN bspec, THEN mp, THEN mp],
       erule_tac [5] asm_rl)
apply (drule_tac [2] bspec [THEN bspec, THEN mp, THEN mp],
       erule_tac [4] asm_rl)
apply (drule_tac [1] bspec [THEN bspec, THEN mp, THEN mp],
       erule_tac [3] asm_rl)
apply safe
apply (assumption | rule exI dBoundBy_dLamI2 dBoundBy_dAppI1
         dBoundBy_dAppI2)+
done

lemma dProp_dBoundBy_lemma1:
  assumes major: "M: dProp"
  and prem: "<m, TdBound(n)>: dOcc(M)"
  shows "EX l. dBoundBy(<m, TdBound(n)>, <l, TdLam>, M)"
apply (rule major [THEN dPropE])
apply (insert dDeg_dLamDeg_lemma1 [OF major [THEN dPropD1] prem])
apply (rule dBoundBy_dLamDeg_lemma2)
prefer 3 apply simp
apply (assumption | rule prem)+
done

lemma dProp_dBoundBy_lemma2:
  assumes major: "M: dTerm"
  and prem:
     "ALL m n. <m, TdBound(n)>: dOcc(M) -->
          (EX l. dBoundBy(<m, TdBound(n)>, <l, TdLam>, M))"
  shows "M: dProp"
apply (case_tac "EX l n. <l, TdBound(n)>: dOcc(M)")
prefer 2
apply (drule major [THEN dDeg_0_lemma])
apply (drule_tac [2] major [THEN dDeg_dLamDeg_lemma2])
apply (erule_tac [2] exE conjE)+
apply (rule_tac [2] prem [THEN spec, THEN spec, THEN mp, THEN exE])
prefer 2 apply assumption
apply (drule_tac [2] dBoundBy_dLamDeg_lemma1)
apply (rotate_tac [2] 2)
prefer 2 apply simp
apply (assumption | rule dPropI major)+
done

lemma dOcc_dAbstI1:
  assumes prem1: "<l, TdVar(x)>: dOcc(M)"
  and prem2: "M: dTerm"
  and prem3: "n: nat"
  shows "<l, TdBound(n #+ dLamDeg(l, M))>: dOcc(dAbst(M, x, n))"
apply (rule prem1 [THEN rev_mp])
apply (rule_tac x="l" and A="list(nat)" in bspec)
apply (rule_tac [2] dOcc_typeD1 [OF prem1 prem2])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem2 [THEN dTerm.induct])
apply (safe elim!: dOcc_dTermEs dTag.free_elims ConsE)
apply simp_all
apply (rule_tac [4] dOcc_dTermIs)
apply (rule_tac [3] dOcc_dTermIs)
apply (rule_tac [2] dOcc_dTermIs)
apply (rule_tac [1] dOcc_dTermIs)
apply (drule bspec [THEN bspec, THEN mp])
prefer 3 apply assumption
apply (erule nat_succI)
prefer 2 apply simp
apply assumption
apply (erule_tac [2] bspec [THEN bspec, THEN mp])
apply (erule_tac [1] bspec [THEN bspec, THEN mp])
apply assumption+
done

lemma dOcc_dAbstI2:
  assumes prem1: "<l, T>: dOcc(M)"
  and major: "T ~= TdVar(x)"
  and prem2: "M: dTerm"
  and prem3: "n: nat"
  shows "<l, T>: dOcc(dAbst(M, x, n))"
apply (insert major)
apply (rule prem1 [THEN rev_mp])
apply (rule_tac x="l" and A="list(nat)" in bspec)
apply (rule_tac [2] dOcc_typeD1 [OF prem1 prem2])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem2 [THEN dTerm.induct])
apply (safe elim!: dOcc_dTermEs dTag.free_elims ConsE)
apply (subgoal_tac "x ~= xa")
prefer 2 apply blast
apply simp_all
apply (safe intro!: dOcc_dTermIs)
apply (erule_tac [3] bspec [THEN bspec, THEN mp])
apply (erule_tac [2] bspec [THEN bspec, THEN mp])
apply (erule_tac [1] bspec [THEN bspec, THEN mp])
apply (assumption | rule nat_succI)+
done

lemma dOcc_dAbstE_lemma:
  assumes major: "<l, T>: dOcc(dAbst(M, x, n))"
  and prem1: "M: dTerm"
  and prem2: "n: nat"
  and prem3:
   "T = TdBound(n #+ dLamDeg(l, M)) & <l, TdVar(x)>: dOcc(M) --> R"
  and prem4: "<l, T>: dOcc(M) --> R"
  shows "R"
apply (rule prem4 [THEN rev_mp])
apply (rule prem3 [THEN rev_mp])
apply (rule major [THEN rev_mp])
apply (rule_tac x="l" and A="list(nat)" in bspec)
prefer 2
apply (rule major [THEN dOcc_typeD1])
apply (assumption | rule dAbst_type prem1 prem2)+
apply (rule prem2 [THEN [2] bspec])
apply (rule prem1 [THEN dTerm.induct])
apply (case_tac "x = xa")
apply simp_all
apply (safe elim!: dOcc_dTermEs dTag.free_elims ConsE
         intro!: dOcc_dTermIs)
apply simp_all
apply (drule_tac [2] bspec [THEN bspec])
apply (erule_tac [2] nat_succI)
apply (drule_tac [1] bspec [THEN bspec])
apply (erule_tac [1] nat_succI)
apply assumption
prefer 2 apply assumption
apply simp
apply simp
apply blast
apply blast
done

lemma dOcc_dAbstE:
  assumes major: "<l, T>: dOcc(dAbst(M, x, n))"
  and prem1: "M: dTerm"
  and prem2: "n: nat"
  and prem3:
   "[| T = TdBound(n #+ dLamDeg(l, M)); <l, TdVar(x)>: dOcc(M) |] ==> R"
  and prem4: "<l, T>: dOcc(M) ==> R"
  shows "R"
apply (rule dOcc_dAbstE_lemma [OF major prem1 prem2])
apply (rule_tac [2] impI)
apply (rule impI)
apply (erule conjE)
apply (erule_tac [2] prem4)
apply (erule prem3)
apply assumption
done

lemma dOcc_dAbst_lemma1:
  assumes major: "<l, T>: dOcc(dAbst(M, x, n))"
  and prem1: "M: dTerm"
  and prem2: "n: nat"
  shows "T ~= TdVar(x)"
apply (rule major [THEN rev_mp])
apply (rule_tac x="l" in spec)
apply (rule_tac prem2 [THEN [2] bspec])
apply (rule prem1 [THEN dTerm.induct])
apply (case_tac "x = xa")
prefer 2
apply (simp_all del: all_simps)
apply (safe elim!: dOcc_dTermEs dTag.free_elims)
apply (drule_tac [3] bspec [THEN spec, THEN mp],
       erule_tac [4] asm_rl) 
apply (drule_tac [2] bspec [THEN spec, THEN mp],
       erule_tac [3] asm_rl) 
apply (drule_tac [1] bspec [THEN spec, THEN mp],
       erule_tac [2] asm_rl)
prefer 3
prefer 5
apply (assumption | rule nat_succI)+
apply (erule notE, rule refl)+
done

lemma dOcc_dAbst_lemma2:
  assumes major: "<l, TdBound(n #+ dLamDeg(l, M))>: dOcc(dAbst(M, x, n))"
  and prem1: "M: dTerm"
  and prem2: "n: nat"
  and prem3: "dDeg(M) le n"
  shows "<l, TdVar(x)>: dOcc(M)"
apply (rule major [THEN rev_mp])
apply (rule prem3 [THEN rev_mp])
apply (rule_tac x="l" and A="list(nat)" in bspec)
prefer 2
apply (rule major [THEN dOcc_typeD1])
apply (assumption | rule dAbst_type prem1 prem2)+
apply (rule prem2 [THEN [2] bspec])
apply (rule prem1 [THEN dTerm.induct])
apply (case_tac "x = xa")
prefer 2
apply simp_all
apply (safe elim!: dOcc_dTermEs dTag.free_elims ConsE
            intro!: dOcc_dTermIs)
apply simp_all
apply (erule bspec [THEN mp, THEN bspec, THEN mp])
apply (erule nat_succI)
prefer 3 apply simp
apply assumption+
done

lemma dOcc_dAbst_lemma3:
  assumes major: "<l, TdBound(dLamDeg(l, M))>: dOcc(dAbst(M, x, 0))"
  and prem: "M: dProp"
  shows "<l, TdVar(x)>: dOcc(M)"
apply (rule prem [THEN dPropE])
apply (rule dOcc_dAbst_lemma2)
prefer 4
apply simp
apply (rule le_refl)
prefer 2
apply simp
apply (assumption | rule major nat_0I Ord_0)+
done

lemma dLamDeg_dAbst_lemma:
  assumes major: "M: dTerm"
  and prem1: "<l, T>: dOcc(M)"
  and prem2: "n: nat"
  shows "dLamDeg(l, dAbst(M, x, n)) = dLamDeg(l, M)"
apply (rule prem1 [THEN rev_mp])
apply (rule prem2 [THEN [2] bspec])
apply (rule_tac x="l" and A="list(nat)" in bspec)
prefer 2
apply (rule dOcc_typeD1 [OF prem1 major])
apply (rule major [THEN dTerm.induct])
apply (safe elim!: dOcc_dTermEs ConsE dTag.free_elims)
apply (case_tac "x = xa")
apply simp_all
done

lemma dBoundBy_dAbstI:
  assumes major: "dBoundBy(u, v, M)"
  and prem: "n: nat"
  shows "dBoundBy(u, v, dAbst(M, x, n))"
apply (rule major [THEN rev_mp])
apply (rule prem [THEN [2] bspec])
apply (rule_tac x="v" in spec)
apply (rule_tac x="u" in spec)
apply (rule major [THEN dBoundByD1, THEN dTerm.induct])
apply (safe elim!: dBoundBy_dTermEs dTag.free_elims)
apply simp_all
apply (safe intro!: dBoundBy_dTermIs dAbst_type)
apply (rule dLamDeg_dAbst_lemma)
apply (assumption | rule nat_succI)+
apply (erule dOcc_dAbstI2)
apply (blast elim!: dTag.free_elims)
apply (assumption | rule nat_succI)+
apply (erule_tac [3] spec [THEN spec, THEN mp, THEN bspec])
apply (erule_tac [2] spec [THEN spec, THEN mp, THEN bspec])
apply (erule_tac [1] spec [THEN spec, THEN mp, THEN bspec])
apply (assumption | rule nat_succI)+
done

lemma dBoundBy_dAbstD:
  assumes major: "dBoundBy(u, v, dAbst(M, x, n))"
  and prem1: "M: dTerm"
  and prem2: "n: nat"
  shows "dBoundBy(u, v, M)"
apply (rule major [THEN rev_mp])
apply (rule prem2 [THEN [2] bspec])
apply (rule_tac x="v" in spec)
apply (rule_tac x="u" in spec)
apply (rule prem1 [THEN dTerm.induct])
apply (case_tac "x = xa")
prefer 2
apply (simp_all del: all_simps ball_simps)
apply (safe elim!: dBoundBy_dTermEs dOcc_dAbstE dTag.free_elims
            intro!: dBoundBy_dTermIs)
apply (assumption | rule dLamDeg_dAbst_lemma [THEN sym] nat_succI)+
apply (drule_tac f="%x. x #- dLamDeg(m, M)" in function_apply_eq)
apply (simp del: all_simps ball_simps add: dLamDeg_dAbst_lemma)
apply (erule_tac [3] spec [THEN spec, THEN bspec, THEN mp],
       erule_tac [4] asm_rl) 
apply (erule_tac [2] spec [THEN spec, THEN bspec, THEN mp],
       erule_tac [3] asm_rl) 
apply (erule_tac [1] spec [THEN spec, THEN bspec, THEN mp],
       erule_tac [2] asm_rl) 
apply (assumption | rule nat_succI)+
done

lemma dFV_dLift_iff:
  assumes prem1: "M: dTerm"
  and prem2: "n: nat"
  shows "x : dFV(dLift(M, n)) <-> x: dFV(M)"
apply (rule prem2 [THEN [2] bspec])
apply (rule prem1 [THEN dTerm.induct])
apply (rule_tac [2] ballI)
apply (case_tac [2] "n < xa")
apply simp_all
done

lemma dFV_dSubst_lemma:
  assumes major: "x: dFV(dSubst(M, n, N))"
  and prem1: "M: dTerm"
  and prem2: "n: nat"
  and prem3: "N: dTerm"
  shows "x: dFV(M) | x: dFV(N)"
apply (rule major [THEN rev_mp])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem2 [THEN [2] bspec])
apply (rule prem1 [THEN dTerm.induct])
apply (rule_tac [2] ballI)
apply (case_tac [2] "xa = n")
apply (case_tac [3] "xa < n")
apply (simp_all del: ball_simps all_simps)
apply safe
apply (drule_tac [3] bspec [THEN bspec, THEN mp],
       erule_tac [5] asm_rl)
apply (drule_tac [2] bspec [THEN bspec, THEN mp],
       erule_tac [4] asm_rl)
apply (drule_tac [1] bspec [THEN bspec, THEN mp],
       erule_tac [3] asm_rl)
prefer 4
prefer 5
prefer 7
prefer 8
apply (assumption | rule dLift_type nat_succI nat_0I)+
apply (simp add: dFV_dLift_iff)
apply safe
done

end
