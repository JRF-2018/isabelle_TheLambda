(*
    File:        FinBnd.thy
    Time-stamp:  <2020-06-22T03:49:39Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory FinBnd imports MonoInj begin

definition FinExt :: "[i,i=>i,i]=>i" where
"FinExt(D, h, X) == {0} Un {x: Pow(D). EX z: X. x <= h(z)}"

definition fin_bnd :: "[i, i=>i]=>o" where
"fin_bnd(x, h) == EX n: nat. x <= nat_rec(n, 0, %n r. h(r))"

definition fin_bnd_set :: "[i, i=>i]=>i" where
"fin_bnd_set(D, h) == {x: Pow(D). fin_bnd(x, h)}"

definition bnd_cont :: "[i, i=>i]=>o" where
    "bnd_cont(D, h) ==   h(D) <= D & 
                       (ALL X:Pow(Pow(D)). X ~= 0 -->   
                                 h(Union(X)) = (UN x: X. h(x)))"

(** bnd_cont(D, h) : h is bound by D and is continuous **)
lemma bnd_contI:
  "[| !!X. [| X <= Pow(D); X ~= 0 |] ==> h(Union(X)) = (UN x: X. h(x));
      h(D) <= D |] ==> bnd_cont(D, h)"
apply (unfold bnd_cont_def)
apply blast
done

lemma bnd_contD1:
    "bnd_cont(D, h) ==> h(D) <= D"
apply (unfold bnd_cont_def)
apply blast
done

lemma bnd_contD2:
    "[| bnd_cont(D, h); X <= Pow(D); X ~= 0 |] ==> 
          h(Union(X)) = (UN x: X. h(x))"
apply (unfold bnd_cont_def)
apply blast
done

lemma bnd_cont_upair:
  "[| bnd_cont(D, h); X <= D; Y <= D |] ==> h(X Un Y) = h(X) Un h(Y)"
apply (unfold Un_def)
apply (erule bnd_contD2 [THEN ssubst])
apply (rule subsetI)
apply (rule PowI)
apply (erule UpairE)
apply simp
apply simp
apply (rule not_emptyI)
apply (rule UpairI1)
apply (rule equalityI)
apply (rule Union_mono)
apply (rule subsetI)
apply (erule RepFunE)
apply (erule UpairE)
apply simp
apply simp
apply (rule Union_mono)
apply (rule subsetI)
apply (erule UpairE)
apply hypsubst
apply (rule RepFunI)
apply (rule UpairI1)
apply hypsubst
apply (rule RepFunI)
apply (rule UpairI2)
done

lemma bnd_cont_bnd_mono:
    "bnd_cont(D, h) ==> bnd_mono(D,h)"
apply (rule bnd_monoI)
apply (erule bnd_contD1)
apply (erule_tac P="%x. h(W) <= h(x)" in subset_Un_iff [THEN iffD1, THEN subst])
apply (erule_tac P="%x. h(W) <= x" in bnd_cont_upair [THEN ssubst])
apply (assumption | (rule Un_upper1))+
done

(** fin_bnd(x, h) : x is finitely bound by h **)
lemma fin_bnd_0:
  "fin_bnd(0, h)"
apply (unfold fin_bnd_def)
apply blast
done

lemma fin_bnd_induct:
  assumes major: "fin_bnd(a, h)"
  and P_0: "P(0)"
  and indstep: "!! x y. [| fin_bnd(x,h); y <= h(x); P(x)|]  ==> P(y)"
  shows "P(a)"
apply (rule major [unfolded fin_bnd_def, THEN bexE])
apply (erule_tac P="a <= nat_rec(x, 0, % n r. h(r))" in rev_mp)
apply (rule allE)
prefer 2 apply assumption
apply (erule nat_induct)
apply (rule allI)
apply (rule nat_rec_0 [THEN ssubst])
apply (rule impI)
apply (drule subset_empty_iff [THEN iffD1])
apply (erule ssubst)
apply (rule P_0)
apply (rule allI)
apply (rule nat_rec_succ [THEN ssubst])
apply assumption
apply (rule impI)
apply (rule indstep [unfolded fin_bnd_def])
prefer 2 apply assumption
apply (rule bexI)
apply (rule subset_refl)
apply assumption
apply (erule allE)
apply (erule mp)
apply (rule subset_refl)
done

lemma fin_bnd_lemma1:
  "[| bnd_mono(D, h); n: nat |] ==> nat_rec(n, 0, %n r. h(r)) <= D"
apply (erule nat_induct)
apply (rule nat_rec_0 [THEN ssubst])
apply (rule empty_subsetI)
apply (erule nat_rec_succ [THEN ssubst])
apply (erule bnd_mono_subset)
apply assumption
done

lemma fin_bnd_lemma2:
  assumes hmono: "bnd_mono(D, h)"
  shows "n: nat ==> 
    nat_rec(n, 0, %l r. h(r)) <= nat_rec(succ(n), 0, %l r. h(r))"
apply (erule nat_induct)
apply (rule nat_rec_0 [THEN ssubst])
apply (rule empty_subsetI)
apply (simp only: nat_rec_succ)
apply (rule hmono [THEN bnd_monoD2])
apply assumption
apply (rule hmono [THEN bnd_mono_subset])
apply (rule hmono [THEN fin_bnd_lemma1])
apply assumption
done

lemma fin_bnd_lemma3 [rule_format]:
 assumes hmono: "bnd_mono(D,h)"
 shows "ALL m: nat. ALL n: nat. n \<le> m -->
        nat_rec(n, 0, %l r. h(r)) <= nat_rec(m, 0, %l r. h(r))"
apply (rule ballI)
apply (erule nat_induct)
apply (intro impI ballI)
apply (drule le_imp_subset)
apply (drule subset_empty_iff [THEN iffD1])
apply hypsubst
apply (rule subset_refl)
apply (intro impI ballI)
apply (drule le_succ_iff [THEN iffD1])
apply (erule disjE)
apply (rule hmono [THEN fin_bnd_lemma2, THEN [2] subset_trans])
prefer 2 apply assumption
apply (erule ballE)
apply (erule mp)
apply assumption
apply (erule notE)
apply assumption
apply (erule conjE)
apply hypsubst
apply (rule subset_refl)
done

lemma fin_bnd_domain:
    "[| bnd_mono(D, h); fin_bnd(x, h) |] ==> x <= D"
apply (unfold fin_bnd_def)
apply (erule bexE)
apply (erule subset_trans)
apply (erule fin_bnd_lemma1)
apply assumption
done

lemma fin_bnd_succ:
  "[| bnd_mono(D,h); fin_bnd(x, h); y <= h(x) |] ==> fin_bnd(y, h)"
apply (unfold fin_bnd_def)
apply (erule bexE)
apply (rule bexI)
apply (rule nat_rec_succ [THEN ssubst])
apply assumption
apply (erule subset_trans)
apply (rule_tac h="h" in bnd_monoD2)
apply (assumption | (rule nat_succI fin_bnd_lemma1))+
done

lemma fin_bnd_subset:
  "[| bnd_mono(D, h); fin_bnd(x, h); y <= x |] ==> fin_bnd(y, h)"
apply (unfold fin_bnd_def)
apply (elim bexE)
apply (rule bexI)
apply (erule subset_trans)
apply assumption+
done

lemma fin_bnd_Un:
    assumes hmono: "bnd_mono(D, h)"
    shows "[| fin_bnd(x, h); fin_bnd(y, h) |] ==>
                fin_bnd(x Un y, h)"
apply (unfold fin_bnd_def)
apply (elim bexE)
apply (rename_tac m)
apply (rule_tac i="n" and j="m" in Ord_linear_le)
apply (erule nat_into_Ord)+
apply (rule bexI)
apply (rule Un_least)
apply (erule subset_trans)
apply (erule_tac [2] subset_trans)
apply (rule hmono [THEN fin_bnd_lemma3])
prefer 3 apply assumption
apply (rule_tac [3] hmono [THEN fin_bnd_lemma3])
apply (assumption | (rule le_refl) | (erule nat_into_Ord))+
apply (rule bexI)
apply (rule Un_least)
apply (erule subset_trans)
apply (erule_tac [2] subset_trans)
apply (rule hmono [THEN fin_bnd_lemma3])
apply (rule_tac [4] hmono [THEN fin_bnd_lemma3])
prefer 6 apply assumption
apply (assumption | (rule le_refl) | (erule nat_into_Ord))+
done

lemma fin_bnd_bound:
  assumes hmono: "bnd_mono(D, h)"
  and fb_a: "fin_bnd(a, h)"
  and fb_z: "!!z. [| a <= h(z); z <= D; fin_bnd(h(z), h) |] ==> P"
  shows "P"
apply (rule fb_a [unfolded fin_bnd_def, THEN bexE])
apply (rule fb_z [unfolded fin_bnd_def])
apply (erule subset_trans)
apply (rule hmono [THEN fin_bnd_lemma2, THEN subset_trans])
apply assumption
apply (simp only: nat_rec_succ)
apply (rule subset_refl)
apply (rule hmono [THEN fin_bnd_lemma1])
apply assumption
apply (rule_tac x="succ(x)" in bexI)
apply (simp only: nat_rec_succ)
apply (rule subset_refl)
apply (rule nat_succI)
apply assumption
done

lemma fin_bnd_bound2:
  assumes hmono: "bnd_mono(D, h)"
  and fb_a: "fin_bnd(a, h)"
  and fb_z: "!!z. [| a <= z; z <= h(z); z <= D; 
               fin_bnd(z, h); fin_bnd(h(z), h) |] ==> P"
  shows "P"
apply (rule fb_a [unfolded fin_bnd_def, THEN bexE])
apply (rule fb_z [unfolded fin_bnd_def])
apply (rule_tac [2]  hmono [THEN fin_bnd_lemma2, THEN subset_trans])
prefer 2 apply assumption
prefer 2 apply (simp only: nat_rec_succ)
apply (rule subset_refl)
apply assumption
apply (rule hmono [THEN fin_bnd_lemma1])
apply assumption
apply (rule_tac x="x" in bexI)
apply (rule subset_refl)
apply assumption
apply (rule_tac x="succ(x)" in bexI)
apply (simp only: nat_rec_succ)
apply (rule subset_refl)
apply (rule nat_succI)
apply assumption
done

(** FinExt(D, h) : the finite extension of h **)
lemma FinExt_bnd_cont:
    "bnd_cont(Pow(D), FinExt(D,h))"
apply (rule bnd_contI)
apply (unfold FinExt_def)
prefer 2 apply blast
apply (rule equalityI)
apply (rule subsetI)
apply (rule_tac [2] subsetI)
apply (erule UnE)
apply (erule not_emptyE)
apply blast
apply (erule CollectE)
apply (erule bexE)
apply (erule UnionE)
apply (erule UN_I)
apply (rule UnI2)
apply (erule CollectI)
apply (erule bexI)
apply assumption
apply (erule UN_E)
apply (erule UnE)
apply (erule UnI1)
apply (rule UnI2)
apply (erule CollectE)
apply (erule bexE)
apply (erule CollectI)
apply (erule bexI)
apply (erule UnionI)
apply assumption
done

lemma FinExt_bnd_mono:
  "bnd_mono(Pow(D), FinExt(D,h))"
apply (rule FinExt_bnd_cont [THEN bnd_cont_bnd_mono])
done

lemma FinExt_lower_Pow_lfp:
  assumes hmono: "bnd_mono(D,h)"
  shows "FinExt(D, h, Pow(lfp(D,h))) <= Pow(lfp(D,h))"
apply (unfold FinExt_def)
apply (rule Un_subset_iff [THEN iffD2])
apply (rule conjI)
apply blast
apply (rule subsetI)
apply (erule CollectE)
apply (erule bexE)
apply ((drule PowD) | (rule PowI))+
apply (erule subset_trans)
apply (rule hmono [THEN lfp_lemma2, THEN [2] subset_trans])
apply (erule hmono [THEN bnd_monoD2])
apply (rule lfp_subset)
done

lemma FinExt_another_def:
  assumes hmono: "bnd_mono(D,h)"
  and dom_X: "X <= Pow(D)"
  shows "FinExt(D, h, X) = {0} Un (UN z: X. Pow(h(z)))"
apply (unfold FinExt_def)
apply (rule equalityI)
apply (rule_tac [2] subset_refl [THEN Un_mono])
apply (rule_tac [1] subset_refl [THEN Un_mono])
apply (rule_tac [2] subsetI)
apply (rule subsetI)
apply (elim CollectE bexE)
apply (erule UN_I)
apply (erule PowI)
apply (erule UN_E)
apply (rule CollectI)
apply (drule dom_X [THEN subsetD])
apply (drule_tac [2] PowD)
apply (drule PowD)+
apply (rule PowI)
apply (erule subset_trans)
apply (erule hmono [THEN bnd_mono_subset])
apply (erule bexI)
apply assumption
done

(** fin_bnd_set and FinExt **)
lemma fin_bnd_set_domain:
    "fin_bnd_set(D, h) <= Pow(D)"
apply (unfold fin_bnd_set_def)
apply (rule Collect_subset)
done

lemma fin_bnd_set_0I:
    "0: fin_bnd_set(D, h)"
apply (unfold fin_bnd_set_def)
apply (rule CollectI)
apply (rule empty_subsetI [THEN PowI])
apply (rule fin_bnd_0)
done

lemma fin_bnd_setI:
  "[| a <= D; fin_bnd(a, h) |] ==> a: fin_bnd_set(D, h)"
apply (unfold fin_bnd_set_def)
apply (erule PowI [THEN CollectI])
apply assumption
done

lemma fin_bnd_setI2:
  "[| bnd_mono(D, h); fin_bnd(a, h) |] ==> a: fin_bnd_set(D, h)"
apply (unfold fin_bnd_set_def)
apply (rule fin_bnd_domain [THEN PowI, THEN CollectI])
apply assumption+
done

lemma fin_bnd_setD1:
    "a: fin_bnd_set(D, h) ==> a <= D"
apply (unfold fin_bnd_set_def)
apply blast
done

lemma fin_bnd_setD2:
    "a: fin_bnd_set(D, h) ==> fin_bnd(a, h)"
apply (unfold fin_bnd_set_def)
apply blast
done

lemma fin_bnd_setE:
    "[| a: fin_bnd_set(D, h);
        [| a <= D; fin_bnd(a, h)|] ==> P |] ==> P"
apply (unfold fin_bnd_set_def)
apply blast
done

lemma fin_bnd_set_subset_lfp_FinExt:
  assumes hmono: "bnd_mono(D,h)"
  shows "fin_bnd_set(D, h) <= lfp(Pow(D), FinExt(D, h))"
apply (unfold fin_bnd_set_def)
apply (rule subsetI)
apply (erule CollectE)
apply (erule fin_bnd_induct)
apply (rule FinExt_bnd_mono [THEN lfp_lemma2, THEN subsetD])
apply (subst hmono [THEN FinExt_another_def])
apply (rule lfp_subset)
apply (rule UnI1)
apply (rule singletonI)
apply (rule FinExt_bnd_mono [THEN lfp_lemma2, THEN subsetD])
apply (subst hmono [THEN FinExt_another_def])
apply (rule lfp_subset)
apply (rule UnI2)
apply (rule UN_I)
apply (rule_tac [2] PowI)
prefer 2 apply assumption
apply assumption
done

lemma fin_bnd_set_pre_fixedpt:
  assumes hmono: "bnd_mono(D, h)"
  shows "FinExt(D, h, fin_bnd_set(D, h)) <= fin_bnd_set(D, h)"
apply (unfold fin_bnd_set_def)
apply (rule Collect_subset
       [THEN hmono 
            [THEN FinExt_another_def, THEN ssubst]])
apply (rule subsetI)
apply (erule UnE)
apply (erule singletonE)
apply hypsubst
apply (rule CollectI)
apply (rule empty_subsetI [THEN PowI])
apply (rule fin_bnd_0)
apply (erule UN_E)
apply (erule CollectE)
apply (rule CollectI)
apply (drule PowD)+
apply (rule PowI)
apply (rule hmono [THEN bnd_monoD1, THEN [2] subset_trans])
apply (erule subset_trans)
apply (erule hmono [THEN bnd_monoD2])
apply (rule subset_refl)
apply (drule PowD)+
apply (erule hmono [THEN fin_bnd_succ])
apply assumption
done

lemma fin_bnd_set_lfp_eq:
  assumes hmono: "bnd_mono(D, h)"
  shows "fin_bnd_set(D, h) = lfp(Pow(D), FinExt(D, h))"
apply (rule equalityI)
apply (rule hmono [THEN fin_bnd_set_subset_lfp_FinExt])
apply (rule lfp_lowerbound)
apply (rule hmono [THEN fin_bnd_set_pre_fixedpt])
apply (rule fin_bnd_set_domain)
done

lemma fin_bnd_set_Pow_lfp_lowerbound:
  assumes hmono: "bnd_mono(D,h)"
  shows "fin_bnd_set(D, h) <= Pow(lfp(D,h))"
apply (unfold fin_bnd_set_def)
apply (rule subsetI)
apply (erule CollectE)
apply (rule PowI)
apply (drule PowD)
apply (erule fin_bnd_induct)
apply (rule empty_subsetI)
apply (rule hmono [THEN lfp_lemma2, THEN [2] subset_trans])
apply (erule subset_trans)
apply (erule hmono [THEN bnd_monoD2])
apply (rule lfp_subset)
done

lemma Union_fin_bnd_set_pre_fixedpt:
  assumes hcont: "bnd_cont(D, h)"
  shows "h(Union(fin_bnd_set(D, h))) <= Union(fin_bnd_set(D, h))"
apply (rule_tac P="%y. y <= Union(fin_bnd_set(D,h))" in
        hcont [THEN bnd_contD2, THEN ssubst])
apply (rule_tac [2] not_emptyI)
apply (rule_tac [2] fin_bnd_set_0I)
apply (unfold fin_bnd_set_def)
apply (rule Collect_subset)
apply (rule subsetI)
apply (erule UN_E)
apply (erule CollectE)
apply (rule UnionI)
apply (rule CollectI)
prefer 3 apply assumption
apply (drule PowD)
apply (rule PowI)
apply (erule hcont [THEN bnd_cont_bnd_mono, THEN bnd_mono_subset])
apply (erule hcont [THEN bnd_cont_bnd_mono, THEN fin_bnd_succ])
apply (rule subset_refl)
done

lemma Union_fin_bnd_set_lfp_eq:
  assumes hcont: "bnd_cont(D, h)"
  shows "Union(fin_bnd_set(D, h)) = lfp(D, h)"
apply (rule equalityI)
apply (rule_tac P="%x. Union(fin_bnd_set(D, h)) <= x" in
        Union_Pow_eq [THEN subst])
apply (rule hcont [THEN bnd_cont_bnd_mono,
                   THEN fin_bnd_set_Pow_lfp_lowerbound,
                   THEN Union_mono])
apply (rule lfp_lowerbound)
apply (rule hcont [THEN Union_fin_bnd_set_pre_fixedpt])
apply (rule_tac P="%x. Union(fin_bnd_set(D, h)) <= x" in 
        Union_Pow_eq [THEN subst])
apply (rule fin_bnd_set_domain [THEN Union_mono])
done

lemma fin_bnd_set_upper_Fin_lfp:
  assumes hcont: "bnd_cont(D, h)"
  shows "Fin(lfp(D, h)) <= fin_bnd_set(D, h)"
apply (rule subsetI)
apply (erule Fin_induct)
apply (rule fin_bnd_set_0I)
apply (rename_tac v y)
apply (drule_tac P="%x. v: x" in 
  hcont [THEN Union_fin_bnd_set_lfp_eq, THEN ssubst])
apply (erule UnionE)
apply (unfold fin_bnd_set_def)
apply (elim CollectE)
apply (drule PowD)+
apply (rule CollectI)
apply blast
apply (rule hcont [THEN bnd_cont_bnd_mono, THEN fin_bnd_subset])
apply (rule_tac x="B" and y="y" in
        hcont [THEN bnd_cont_bnd_mono, THEN fin_bnd_Un])
apply assumption+
apply (rule cons_eq [THEN subst])
apply (rule Un_mono)
apply (erule singleton_subsetI)
apply (rule subset_refl)
done

(** Induction principles on finitely bound set **)
lemma fin_bnd_set_Collect_is_pre_fixedpt:
  assumes hinj: "mono_inj_pair(D,F,G)"
  and hinjp: "mono_inj_pair(F(D),Fp, Gp)"
  and FG0: "F(G(0)) = 0"
  and hmono: "bnd_mono(D,h)"
  and indstep: "!!x. x : FinExt(F(D), %x. F(h(G(x))),
                       {x: fin_bnd_set(F(D), %x. F(h(G(x)))).
                        (ALL y: Pow(Fp(F(G(x)))). P(Gp(y)))}) ==> P(x)"
  shows "FinExt(F(D), %x. F(h(G(x))),
                       {x: fin_bnd_set(F(D), %x. F(h(G(x)))).
                        (ALL y: Pow(Fp(F(G(x)))). P(Gp(y)))})
             <= {x: fin_bnd_set(F(D), %x. F(h(G(x)))).
                        (ALL y: Pow(Fp(F(G(x)))). P(Gp(y)))}"
apply (rule subsetI)
apply (rule CollectI)
apply (rule hmono [THEN hinj [THEN mono_inj_pair_bnd_mono],
                   THEN fin_bnd_set_pre_fixedpt [THEN subsetD]])
apply (rule FinExt_bnd_mono [THEN bnd_monoD2, THEN subsetD])
apply (rule_tac [2] fin_bnd_set_domain)
prefer 2 apply assumption
apply (rule Collect_subset)
apply (rule ballI)
apply (drule PowD)
apply (rule indstep)
apply (unfold FinExt_def)
apply (erule UnE)
apply (erule singletonE)
apply hypsubst
apply (rule UnI1)
apply (simp only: FG0)
apply (drule hinjp [THEN mono_inj_pairD3])
apply (rule hinjp [THEN mono_inj_pairD2])
apply (rule empty_subsetI)
apply (rule subset_refl)
apply (subst (asm) hinjp [THEN mono_inj_pairD1])
apply (rule empty_subsetI)
apply (drule subset_empty_iff [THEN iffD1])
apply (erule ssubst)
apply (rule singletonI)
apply (elim CollectE bexE)
apply (subgoal_tac "F(G(x)) <= F(D)" "h(G(z)) <= D")
apply (rule UnI2)
apply (rule CollectI)
apply (rule_tac [2] bexI)
apply (rule_tac [3] CollectI)
apply (rule_tac [4] ballI)
apply (erule_tac [4] bspec)
prefer 4 apply assumption
apply (rule PowI)
apply (drule PowD)
apply (rule subset_trans)
apply (rule hinjp [THEN mono_inj_pairD3])
apply assumption
apply (rule hinjp [THEN mono_inj_pairD2])
apply assumption
apply (rule subset_refl)
apply (subst hinjp [THEN mono_inj_pairD1])
apply assumption
apply (rule subset_trans)
apply (rule hinjp [THEN mono_inj_pairD3])
apply assumption
apply (rule hinjp [THEN mono_inj_pairD2])
apply assumption
apply (rule subset_refl)
apply (subst hinjp [THEN mono_inj_pairD1])
apply assumption
apply (rule subset_trans)
apply (rule hinj [THEN mono_inj_pairD2])
apply (rule hinj [THEN mono_inj_pairD3])
apply assumption
apply (rule hinj [THEN mono_inj_pairD2])
apply assumption
apply (rule subset_refl)
apply (subst hinj [THEN mono_inj_pairD1])
apply assumption
apply (subst hinj [THEN mono_inj_pairD1])
apply assumption
apply (rule subset_refl)
apply assumption
apply (rule hmono [THEN bnd_mono_subset])
apply (rule_tac P="%x. G(z) <= x" in hinj [THEN mono_inj_pairD1, THEN subst])
apply (rule subset_refl)
apply (rule hinj [THEN mono_inj_pairD3])
apply (erule fin_bnd_set_domain [THEN subsetD, THEN PowD])
apply (rule subset_refl)
apply (rule hinj [THEN mono_inj_pairD2])
apply (rule_tac P="%y. G(x) <= y" in hinj [THEN mono_inj_pairD1, THEN subst])
apply (rule subset_refl)
apply (rule hinj [THEN mono_inj_pairD3])
apply (erule PowD)
apply (rule subset_refl)+
done

lemma fin_bnd_set_induct_lemma1:
  assumes hinj: "mono_inj_pair(D,F,G)"
  and hinjp: "mono_inj_pair(F(D),Fp, Gp)"
  and FG0: "F(G(0)) = 0"
  and hmono: "bnd_mono(D,h)"
  and P0: "P(0)"
  and indstep: "!!x. [| x <= F(D); EX z: fin_bnd_set(F(D), %x. F(h(G(x)))).
                  x <= F(h(G(z))) &
                  (ALL y. y <= Fp(F(G(z))) --> P(Gp(y)))
                |] ==> P(x)"
  shows "fin_bnd_set(F(D), %x. F(h(G(x)))) <= 
                    {x: fin_bnd_set(F(D), %x. F(h(G(x)))). 
                                     ALL y: Pow(Fp(F(G(x)))). P(Gp(y))}"
apply (rule_tac P="%z. z <= {x: fin_bnd_set(F(D), %x. F(h(G(x)))). 
                                     ALL y: Pow(Fp(F(G(x)))). P(Gp(y))}"
          in mono_inj_pair_bnd_mono [OF hinj hmono, 
                THEN fin_bnd_set_lfp_eq, THEN ssubst])
apply (rule lfp_lowerbound)
apply (rule_tac [2] Collect_subset [THEN subset_trans])
apply (rule_tac [2] fin_bnd_set_domain)
apply (rule fin_bnd_set_Collect_is_pre_fixedpt
          [OF hinj hinjp FG0 hmono])
apply (unfold FinExt_def)
apply (rule indstep)
apply (erule_tac [2] UnE)
apply (erule UnE)
apply blast
prefer 2 apply (erule singletonE)
apply hypsubst
apply (rule_tac x="0" in bexI)
apply (rule conjI)
apply (rule empty_subsetI)
apply (intro allI impI)
apply (rule ssubst)
apply (rule_tac [2] P0)
apply (subst (asm) FG0)
apply (drule hinjp [THEN mono_inj_pairD3])
apply (rule hinjp [THEN mono_inj_pairD2])
apply (rule empty_subsetI)
apply (rule subset_refl)
apply (subst (asm) hinjp [THEN mono_inj_pairD1])
apply (rule empty_subsetI)
apply (erule subset_empty_iff [THEN iffD1])
apply (rule fin_bnd_set_0I)
apply (elim CollectE bexE)
apply (erule PowD)
apply (elim CollectE bexE)
apply blast
done

lemma mono_inj_pair_fin_bnd_set_induct:
  assumes hinj: "mono_inj_pair(D,F,G)"
  and hinjp: "mono_inj_pair(F(D),Fp, Gp)"
  and FG0: "F(G(0)) = 0"
  and hmono: "bnd_mono(D,h)"
  and a_in_fb: "a: fin_bnd_set(F(D), %x. F(h(G(x))))"
  and P0: "P(0)"
  and indstep:
   "!!x. [| x <= F(D); EX z: fin_bnd_set(F(D), %x. F(h(G(x)))).
               x <= F(h(G(z))) & 
          (ALL y. y <= Fp(F(G(z))) --> P(Gp(y)))
    |] ==> P(x)"
  shows "P(a)"
apply (rule hinjp [THEN mono_inj_pairD1, THEN subst])
apply (rule a_in_fb [THEN fin_bnd_set_domain [THEN subsetD], THEN PowD])
apply (rule mono_inj_pair_bnd_mono [THEN fin_bnd_bound,
        OF hinj hmono a_in_fb[unfolded fin_bnd_set_def, THEN CollectD2]])
apply (subgoal_tac "h(G(z)) <= D")
prefer 2 
apply (rule hmono [THEN bnd_mono_subset])
apply (rule_tac P="%x. G(z) <= x" in hinj [THEN mono_inj_pairD1, THEN subst])
apply (rule subset_refl)
apply (erule hinj [THEN mono_inj_pairD3])
apply (rule subset_refl)
apply (rule fin_bnd_set_induct_lemma1 [OF hinj hinjp FG0 hmono,
        THEN subsetD, THEN CollectD2, THEN bspec])
apply (rule P0)
prefer 2 apply (rule fin_bnd_setI)
prefer 2 apply assumption
apply (rule mono_inj_pair_bnd_mono [OF hinj hmono, THEN bnd_mono_subset])
apply assumption
prefer 2 apply (rule PowI)
apply (rule hinjp [THEN mono_inj_pairD2])
apply (subst hinj [THEN mono_inj_pairD1])
apply assumption+
apply (subst hinj [THEN mono_inj_pairD1])
apply assumption
apply (rule mono_inj_pair_bnd_mono [OF hinj hmono, THEN bnd_mono_subset])
apply assumption
apply (rule indstep)
apply assumption+
done

lemmas fin_bnd_set_induct = mono_inj_pair_fin_bnd_set_induct
  [OF trivial_mono_inj_pair trivial_mono_inj_pair refl, rule_format]


lemma mono_inj_pair_fin_bnd_lemma:
  assumes hinj: "mono_inj_pair(D, F, G)"
  and hmono: "bnd_mono(D, h)"
  and prem: "fin_bnd(z, %x. F(h(G(x))))"
  shows "fin_bnd(F(G(z)), %x. F(h(G(x))))"
apply (rule fin_bnd_bound2 [OF mono_inj_pair_bnd_mono [OF hinj hmono] prem])
apply (rename_tac v)
apply (subgoal_tac "h(G(v)) <= D")
apply (rule mono_inj_pair_bnd_mono [OF hinj hmono, THEN fin_bnd_succ])
apply (rule_tac [2]  hinj [THEN mono_inj_pairD2])
apply (rule_tac [2] P="%x. G(z) <= x" in hinj [THEN mono_inj_pairD1, THEN subst])
apply (rule_tac [3] hinj [THEN mono_inj_pairD3])
apply (erule_tac [3] subset_trans)
apply (rule_tac [4] hinj [THEN mono_inj_pairD2])
prefer 3 apply assumption
apply (assumption | (rule subset_refl))+
apply (rule hmono [THEN bnd_mono_subset])
apply (rule_tac P="%x. G(v) <= x" in hinj [THEN mono_inj_pairD1, THEN subst])
apply (rule_tac [2] hinj [THEN mono_inj_pairD3])
apply (assumption | (rule subset_refl))+
done

lemma fin_bnd_set_succI:
  assumes hmono: "bnd_mono(D, h)"
  and major: "Y <= h(X)"
  and prem: "X: fin_bnd_set(D, h)"
  shows "Y: fin_bnd_set(D, h)"
apply (rule hmono [THEN fin_bnd_setI2])
apply (rule fin_bnd_succ [OF hmono prem [THEN fin_bnd_setD2]])
apply (rule major)
done

lemma fin_bnd_set_UnI:
  assumes hmono: "bnd_mono(D, h)"
  and prem1: "X: fin_bnd_set(D,h)"
  and prem2: "Y: fin_bnd_set(D, h)"
  shows "X Un Y: fin_bnd_set(D, h)"
apply (rule hmono [THEN fin_bnd_setI2])
apply (rule hmono [THEN fin_bnd_Un])
apply (rule prem1 [THEN fin_bnd_setD2])
apply (rule prem2 [THEN fin_bnd_setD2])
done

lemma fin_bnd_set_subsetI:
  assumes hmono: "bnd_mono(D, h)"
  and major: "Y <= X"
  and prem: "X: fin_bnd_set(D,h)"
  shows "Y: fin_bnd_set(D, h)"
apply (rule hmono [THEN fin_bnd_setI2])
apply (rule fin_bnd_subset [OF hmono prem [THEN fin_bnd_setD2] major])
done

lemma fin_bnd_set_boundE:
  assumes hmono: "bnd_mono(D, h)"
  and major: "a: fin_bnd_set(D, h)"
  and prem: "!!z. [| a <= z; z <= h(z); z: fin_bnd_set(D, h); 
               h(z): fin_bnd_set(D, h) |] ==> P"
  shows "P"
apply (rule fin_bnd_bound2 [OF hmono major [THEN fin_bnd_setD2]])
apply (rule prem)
apply (assumption | (rule hmono [THEN fin_bnd_setI2]))+
done

end
