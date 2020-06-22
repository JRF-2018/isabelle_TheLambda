(*
    File:        MonoInj.thy
    Time-stamp:  <2015-12-12T08:36:39Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory MonoInj imports Fixedpt Finite begin

definition mono_inj_pair :: "[i,i=>i,i=>i]=>o" where 
 "mono_inj_pair(D,F,G) == (ALL x. x <= D --> G(F(x)) = x) &   
        (ALL x y. x <= y & y <= D --> F(x) <= F(y)) &   
        (ALL x y. x <= y & y <= F(D) --> G(x) <= G(y))"

lemma lfpI:
  assumes hmono: "bnd_mono(D,h)"
      and lb: "!!X. [| X <= D;  h(X) <= X |] ==> A <= X"
      and pfp: "h(A) <= A"
  shows "lfp(D,h) = A"
apply (rule equalityI)
apply (rule lfp_lowerbound)
apply (rule pfp)
apply (rule lb)
apply (rule subset_refl)
apply (rule hmono [THEN bnd_monoD1])
apply (rule lfp_greatest)
apply (rule hmono [THEN bnd_monoD1])
apply (rule lb)
apply assumption+
done

lemma mono_inj_pairI:
    "[| !!x. x <= D ==> G(F(x)) = x; 
        !!x y. [| x <= y; y <= D |] ==> F(x) <= F(y); 
        !!x y. [| x <= y; y <= F(D) |] ==> G(x) <= G(y) 
    |] ==> mono_inj_pair(D,F,G)"
apply (unfold mono_inj_pair_def)
apply auto
done

lemma mono_inj_pairD1:
    "[| mono_inj_pair(D,F,G); x <= D |] ==> G(F(x)) = x"
apply (unfold mono_inj_pair_def)
apply auto
done

lemma mono_inj_pairD2:
    "[| mono_inj_pair(D,F,G); x <= y; y <= D |] ==> F(x) <= F(y)"
apply (unfold mono_inj_pair_def)
apply auto
done

lemma mono_inj_pairD3:
    "[| mono_inj_pair(D,F,G); x <= y; y <= F(D) |] ==> G(x) <= G(y)"
apply (unfold mono_inj_pair_def)
apply auto
done

lemma mono_inj_pair_lfp_subset:
    "mono_inj_pair(D,F,G) ==> F(lfp(D,h)) <= F(D)"
apply (erule mono_inj_pairD2)
apply (rule lfp_subset)
apply (rule subset_refl)
done

lemma mono_inj_pair_bnd_mono:
  assumes hinj: "mono_inj_pair(D,F,G)"
      and hmono: "bnd_mono(D,h)"
    shows "bnd_mono(F(D), %X. F(h(G(X))))"
apply (rule bnd_monoI)
apply (rule hinj [THEN mono_inj_pairD1, THEN ssubst])
apply (rule subset_refl)
apply (rule hinj [THEN mono_inj_pairD2])
apply (rule hmono [THEN bnd_monoD1])
apply (rule subset_refl)
apply (frule_tac x="X" in hinj [THEN mono_inj_pairD3])
apply (rule subset_refl)
apply (subst (asm) hinj [THEN mono_inj_pairD1])
apply (rule subset_refl)
apply (rule hinj [THEN mono_inj_pairD2])
apply (rule hmono [THEN bnd_monoD2])
apply (rule hinj [THEN mono_inj_pairD3])
apply assumption+
apply (rule hmono [THEN bnd_mono_subset])
apply assumption
done

lemma mono_inj_pair_pre_fixedpt:
  assumes hinj: "mono_inj_pair(D,F,G)"
      and hmono: "bnd_mono(D,h)"
    shows "F(h(G(F(lfp(D,h))))) <= F(lfp(D,h))"
apply (rule hinj [THEN mono_inj_pairD2])
apply (rule hinj [THEN mono_inj_pairD1, THEN ssubst])
apply (rule lfp_subset)
apply (rule hmono [THEN lfp_lemma2])
apply (rule lfp_subset)
done

lemma mono_inj_pair_lfp_lemma1:
  assumes hinj: "mono_inj_pair(D,F,G)"
      and hmono: "bnd_mono(D,h)"
      and dom_x: "X <= F(D)"
      and x_is_pfp: "F(h(G(X))) <= X"
    shows "h(h(G(X))) <= h(G(X))"
apply (subgoal_tac "G(X) <= D")
prefer 2
apply (rule hinj [THEN mono_inj_pairD1, THEN subst])
apply (rule subset_refl)
apply (rule hinj [THEN mono_inj_pairD3])
apply (rule dom_x)
apply (rule subset_refl)
apply (rule_tac P="%x. h(x) <= h(G(X))" in hinj [THEN mono_inj_pairD1, THEN subst])
apply (rule hmono [THEN bnd_mono_subset])
apply assumption
apply (rule hmono [THEN bnd_monoD2])
apply (rule hinj [THEN mono_inj_pairD3])
apply (rule x_is_pfp)
apply (rule dom_x)
apply assumption
done

lemma mono_inj_pair_lfp_lowerbound:
  assumes hinj: "mono_inj_pair(D,F,G)"
      and hmono: "bnd_mono(D,h)"
      and dom_x: "X <= F(D)"
      and x_is_pfp: "F(h(G(X))) <= X"
    shows "F(lfp(D,h)) <= X"
apply (subgoal_tac "h(G(X)) <= D")
prefer 2
apply (rule hmono [THEN bnd_mono_subset])
apply (rule hinj [THEN mono_inj_pairD1, THEN subst])
apply (rule subset_refl)
apply (rule hinj [THEN mono_inj_pairD3])
apply (rule dom_x)
apply (rule subset_refl)
apply (rule subset_trans [OF _ x_is_pfp])
apply (rule hinj [THEN mono_inj_pairD2])
apply (rule lfp_lowerbound)
apply (rule hinj [THEN mono_inj_pair_lfp_lemma1])
apply (rule hmono)
apply ((rule dom_x x_is_pfp) | assumption)+
done

lemma mono_inj_pair_lfp_eq:
  assumes hinj: "mono_inj_pair(D,F,G)"
      and hmono: "bnd_mono(D,h)"
    shows "lfp(F(D), %X. F(h(G(X)))) = F(lfp(D,h))"
apply (rule lfpI)
apply (rule mono_inj_pair_bnd_mono [OF hinj hmono])
apply (rule mono_inj_pair_lfp_lowerbound [OF hinj hmono])
apply assumption+
apply (rule mono_inj_pair_pre_fixedpt [OF hinj hmono])
done

lemma trivial_mono_inj_pair:
    "mono_inj_pair(D, %x. x, %x. x)"
apply (rule mono_inj_pairI)
apply (rule refl)
apply assumption+
done

lemma Pow_Union_mono_inj_pair:
    "mono_inj_pair(D, Pow, Union)"
apply (rule mono_inj_pairI)
apply (rule Union_Pow_eq)
apply (rule Pow_mono)
apply assumption
apply (rule Union_mono)
apply assumption
done

lemma Prod_range_mono_inj_pair:
    "b: B ==> mono_inj_pair(D, %X. B * X, range)"
apply (rule mono_inj_pairI)
apply (erule range_of_prod)
apply (rule Sigma_mono)
apply (rule_tac [3] range_mono)
apply (rule subset_refl)
apply assumption+
done

lemma Prod_domain_mono_inj_pair:
    "b: B ==> mono_inj_pair(D, %X. X * B, domain)"
apply (rule mono_inj_pairI)
apply (erule domain_of_prod)
apply (rule Sigma_mono)
apply (rule_tac [3] domain_mono)
apply ((rule subset_refl) | assumption)+
done

end
