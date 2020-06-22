(*
    File:        PowInd.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open PowInd;

(** Powerset induction principle **)

val mono_inj_pair_Union_lemma = prove_goal PowInd.thy
    "[| mono_inj_pair(D,F,G); mono_inj_pair(F(D), Fp, Gp); bnd_mono(D,h)|] \
\	 ==> h(G(Union({x: Pow(F(lfp(D,h))). \
\		ALL y: Pow(Fp(F(G(x)))). P(y)}))) <= D"
  (fn [hinj, hinjp, hmono] =>
    [(rtac (hmono RS bnd_mono_subset) 1),
     (rtac subset_trans 1),
     (rtac (hinj RS mono_inj_pairD3) 1),
     (rtac ((hinj RS mono_inj_pairD1) RS ssubst) 3),
     (REPEAT (rtac subset_refl 2)),
     (rtac (Union_subset_iff RS iffD2) 1),
     (rtac ballI 1),
     (etac CollectE 1),
     (dtac PowD 1),
     (etac subset_trans 1),
     (rtac (hinj RS mono_inj_pairD2) 1),
     (rtac lfp_subset 1),
     (rtac subset_refl 1)]);

qed_goal "mono_inj_pair_Pow_pre_fixedpt_lemma" PowInd.thy
    "[| mono_inj_pair(D,F,G); mono_inj_pair(F(D),Fp, Gp); bnd_mono(D,h);\
\       !!x. x : Pow(F(h(G((Union(Collect(Pow(F(lfp(D,h))),\
\			   %x. ALL y: Pow(Fp(F(G(x)))). P(Gp(y))))))))) \
\	 ==> P(x) \
\    |] ==> Pow(F(h(G(Union(Collect(Pow(F(lfp(D,h))),\
\			%x. ALL y: Pow(Fp(F(G(x)))). P(Gp(y)))))))) <= \
\   Collect(Pow(F(lfp(D,h))), %x. ALL y: Pow(Fp(F(G(x)))). P(Gp(y)))"
  (fn [hinj, hinjp, hmono,indstep] =>
    [(rtac subsetI 1),
     (rtac CollectI 1),
     (rtac ([hinj, hmono] MRS mono_inj_pair_lfp_eq RS subst) 1),
     (rtac (hmono RS (hinj RS mono_inj_pair_bnd_mono)
	    RS ((Pow_Union_mono_inj_pair RS 
		mono_inj_pair_pre_fixedpt) RS subsetD)) 1),
     (rtac (hmono RS (hinj RS mono_inj_pair_bnd_mono)
	    RS ((Pow_Union_mono_inj_pair RS
		mono_inj_pair_bnd_mono) RS bnd_monoD2 RS subsetD)) 1),
     (rtac Pow_mono 2),
     (TRYALL (ares_tac [Collect_subset, lfp_subset])),
     (rtac ([hinj, hmono] MRS mono_inj_pair_lfp_eq RS subst) 1),
     (rtac Collect_subset 1),
     (rtac ballI 1),
     (rtac indstep 1),
     (asm_full_simp_tac (ZF_ss addsimps [Pow_iff]) 1),
     (res_inst_tac [("P", "%x. ?X <= x")] 
      (hinjp RS mono_inj_pairD1 RS subst) 1),
     (rtac (hinjp RS mono_inj_pairD3) 2),
     (etac subset_trans 2),
     (rtac (hinjp RS mono_inj_pairD2) 2),
     (rtac (hinj RS mono_inj_pairD2) 2),
     (res_inst_tac [("P", "%x. ?X <= x")] 
      (hinj RS mono_inj_pairD1 RS subst) 2),
     (rtac (hinj RS mono_inj_pairD3) 3),
     (rtac (hinjp RS mono_inj_pairD2) 7),
     (REPEAT (ares_tac [subset_refl, hmono RS (hinjp RS (hinj RS 
		mono_inj_pair_Union_lemma)), hinj RS mono_inj_pairD2] 1))]);


qed_goal "mono_inj_pair_Pow_lfp_induct" PowInd.thy
    "[| mono_inj_pair(D,F,G); mono_inj_pair(F(D), Fp, Gp); \
\	bnd_mono(D,h); a <= F(lfp(D,h)); \
\       !!x. x <= F(h(G(Union(Collect(Pow(F(lfp(D,h))),\
\		   %z. ALL y: Pow(Fp(F(G(z)))). P(Gp(y))))))) ==> P(x) \
\    |] ==> P(a)"
  (fn [hinj, hinjp, hmono, a_in_powlfp, indstep] =>
    [(rtac ((hinjp RS mono_inj_pairD1) RS subst) 1),
     (rtac (a_in_powlfp RS subset_trans) 1),
     (rtac (hinj RS mono_inj_pairD2) 1),
     (rtac lfp_subset 1),
     (rtac subset_refl 1),
     (rtac (([hinjp, hmono] MRS 
		(hinj RS mono_inj_pair_Pow_pre_fixedpt_lemma))
      RS (read_instantiate [("h", "%x. Pow(F(h(G(Union(x)))))")]
	  lfp_lowerbound) RS subsetD RS CollectD2 RS bspec) 1),
     (rtac indstep 1),
     (dtac PowD 1),
     (atac 1),
     (rtac PowI 3),
     (rtac (hinjp RS mono_inj_pairD2) 3),
     (rtac subset_trans 1),
     (rtac Collect_subset 1),
     (rtac Pow_mono 1),
     (rtac (([hinj, hmono] MRS mono_inj_pair_bnd_mono)
	     RS (Pow_Union_mono_inj_pair RS
		     mono_inj_pair_lfp_eq) RS ssubst) 2),
     (rtac PowI 2),
     (res_inst_tac [("P", "%x. ?X <= x")]
      (([hinj, hmono] MRS mono_inj_pair_lfp_eq) RS ssubst) 2),
     (rtac subset_refl 2),
     (rtac ((hinj RS mono_inj_pairD1) RS ssubst) 2),
     (rtac ((hinj RS mono_inj_pairD1) RS ssubst) 4),
     (REPEAT (ares_tac [a_in_powlfp, lfp_subset, subset_refl,
			hinj RS mono_inj_pairD2] 1))]);

qed_goal "Pow_lfp_induct" PowInd.thy
    "[| bnd_mono(D,h); a <= lfp(D,h); \
\       !!x. x <= h(Union(Collect(Pow(lfp(D,h)),\
\			   %x. ALL y: Pow(x). P(y)))) ==> P(x) \
\    |] ==> P(a)"
  (fn prems =>
    [(rtac (trivial_mono_inj_pair RS 
	    (trivial_mono_inj_pair RS mono_inj_pair_Pow_lfp_induct)) 1),
     (REPEAT (ares_tac prems 1))]);
