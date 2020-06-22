(*
    File:        ZF_aux.thy
    Time-stamp:  <2016-01-06T17:35:18Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory ZF_aux imports ZF Nat_ZF Arith begin

lemma function_apply_eq:
    "a = b ==> f(a) = f(b)"
by (erule subst_context)

lemma singleton_iff2:
    "{A} = {B} <-> A = B"
apply blast
done

lemma Pow_Un_0_simps:
  "Pow(A) Un {0} = Pow(A)"
  "{0} Un Pow(A) = Pow(A)"
by blast+

lemmas succ_neq_self_simps = succ_neq_self succ_neq_self[THEN not_sym]

(** disjoint **)
lemma disjointI:
    "[| !!x. [| x: X; x: Y |] ==> False |] ==> X Int Y = 0"
by blast

lemma disjointE:
    "[| A Int B = 0; x: A; x: B |] ==> R"
by blast

lemma disjoint_sym:
    "A Int B = 0 ==> B Int A = 0"
by blast

lemma disjoint_subset:
    "[| A Int B = 0; C <= A; D <= B |] ==> C Int D = 0"
by blast

lemma disjoint_UnI:
    "[| A Int C = 0; B Int C = 0 |] ==> (A Un B) Int C = 0"
by blast

lemma disjoint_Un_iff:
    "(A Un B) Int C = 0 <-> A Int C = 0 & B Int C = 0"
by blast

lemma disjoint_Un_iff2:
  "A Int (B Un C) = 0 <-> A Int B = 0 & A Int C = 0"
by blast

lemma disjoint_cons_iff:
    "cons(a, A) Int B = 0 <-> a ~: B & A Int B = 0"
by blast

lemma disjoint_cons_iff2:
    "A Int cons(b, B) = 0 <-> A Int B = 0 & b ~: A"
by blast

(** continuous **)
lemma domain_continuous:
    "domain(Union(X)) = (UN x: X. domain(x))"
by blast

lemma continuous_simps_1:
  "{f(x). x: {g(y). y: X}} = {f(g(y)). y: X}"
  "Union(X) * A = (UN x: X. x * A)"
by blast+

lemmas continuous_simps = domain_continuous
                          continuous_simps_1

(** Nat **)
lemma mem_nat_in_nat:
    "[| a: b; b: nat |] ==> a: nat"
apply (rule lt_nat_in_nat)
apply (erule ltI)
apply (erule nat_into_Ord)
apply assumption
done

lemma lt_Un_eq_lemma:
    "A < B ==> A Un B = B"
apply (frule leI [THEN le_imp_subset])
apply blast
done

lemma le_Un_eq_lemma:
    "A le B ==> A Un B = B"
apply (frule le_imp_subset)
apply blast
done

lemma nat_succ_Un:
  "[| A: nat; B: nat |] ==> succ(A) Un succ(B) = succ(A Un B)"
apply (erule nat_into_Ord [THEN Ord_linear_lt])
apply (erule nat_into_Ord)
prefer 2
apply hypsubst
apply blast
apply (rule lt_Un_eq_lemma [THEN ssubst], assumption)
apply (drule succ_leI)
apply (drule lt_Un_eq_lemma, assumption)
apply (rule trans[OF Un_commute lt_Un_eq_lemma, THEN ssubst], assumption)
apply (drule succ_leI)
apply (drule trans[OF Un_commute lt_Un_eq_lemma], assumption)
done

lemma nat_UnI:
    "[| A: nat; B: nat |] ==> A Un B: nat"
apply (rule_tac i="A" and j="B" in Ord_linear_lt)
apply (erule nat_into_Ord)
apply (erule nat_into_Ord)
apply (drule_tac [3] lt_Un_eq_lemma)
apply (drule lt_Un_eq_lemma)
apply (simp_all add: Un_commute)
done

lemma gt_not_eq:
    "[| p < n; n:nat|]==> n~=p"
by blast

lemma lt_asym_if:
    "p < n ==> if (n < p, a, b) = b"
by (blast elim: lt_asym intro: if_not_P)

lemma le_asym_if:
    "p le n ==> if (n < p, a, b) = b"
apply (simp only: le_iff)
apply (blast elim: lt_asym intro: if_not_P)
done

lemma lt_irrefl_if:
    "if (n < n, a, b) = b"
by (blast intro: if_not_P)

(** Arith **)
lemma succ_pred:
    "[|j:nat; i:nat|]==> i < j --> succ(j #- 1) = j"
apply (erule nat_induct)
apply blast
apply simp
done

lemma lt_pred:
  "[|succ(x)<n; n:nat; x:nat|]==> x < n#-1 "
apply (rule succ_leE)
apply (frule nat_into_Ord [THEN le_refl, THEN lt_trans], assumption)
apply (simp add: succ_pred)
done

lemma gt_pred:
    "[|n < succ(x); p<n; p:nat; n:nat; x:nat|]==> n#-1 < x "
apply (rule succ_leE)
apply (simp add: succ_pred)
done

lemma lt_imp_le_pred:
    "[| i < j; j: nat |] ==> i le j #- 1"
apply (erule natE)
apply simp_all
done

lemma diff_eq_0D:
    "[| m #- n = 0; m: nat; n: nat |] ==> m le n"
apply (erule rev_mp)
apply (rule_tac x="m" in bspec)
prefer 2
apply assumption
apply (erule_tac n="n" in nat_induct)
apply (rule_tac [2] ballI)
apply (rename_tac [2] v)
apply (erule_tac [2] n="v" in natE)
apply simp_all
done

lemma Un_diff [rule_format]:
  assumes prem: "m: nat"
  shows "ALL n:nat. ALL l:nat. (m Un n) #- l = (m #- l) Un (n #- l)"
apply (rule prem [THEN nat_induct])
apply simp
apply (intro ballI)
apply (erule_tac n="n" in natE)
apply (erule_tac [2] n="l" in natE)
apply (simp_all add: nat_succ_Un)
done

lemma Un_least_ltE:
    "[| i Un j < k; Ord(i); Ord(j); 
       [| i < k; j < k |] ==> R |] ==> R"
apply (frule_tac i1="i" and j1="j" in Un_least_lt_iff [THEN iffD1])
apply assumption+
apply blast
done

lemma diff_le_mono1:
  assumes major: "i le j"
      and prem1: "i: nat"
      and prem2: "j: nat"
      and prem3: "k: nat"
  shows "i #- k le j #- k"
apply (rule major [THEN rev_mp])
apply (rule prem2 [THEN [2] bspec]) 
apply (rule prem3 [THEN [2] bspec]) 
apply (rule prem1 [THEN nat_induct])
apply simp
apply (intro ballI impI)
apply (rename_tac u v)
apply (erule_tac n="u" in natE)
apply (erule_tac [2] n="v" in natE)
apply simp_all
done

lemma diff_ltD:
  assumes major: "i #- j < k"
      and prem1: "i: nat"
      and prem2: "j: nat"
  shows "k: nat ==> i < j #+ k"
apply (rule major [THEN rev_mp])
apply (rule prem1 [THEN [2] bspec])
apply (rule prem2 [THEN nat_induct])
apply simp
apply (intro ballI impI)
apply (rename_tac v)
apply (erule_tac n="v" in natE)
apply simp_all
done

lemma diff_leI:
  assumes major: "i le j #+ k"
      and prem1: "i: nat"
      and prem2: "j: nat"
    shows "k: nat  ==> i #- j le k"
apply (rule major [THEN rev_mp])
apply (rule prem1 [THEN [2] bspec])
apply (rule prem2 [THEN nat_induct])
apply simp
apply (intro ballI impI)
apply (rename_tac v)
apply (erule_tac n="v" in natE)
apply simp_all
done

lemma diff_le_iff:
    "[| i: nat; j: nat; k: nat |] ==> i #- j le k <-> i le j #+ k"
apply (rule iffI)
apply (rule_tac [2] diff_leI)
apply (drule diff_ltD)
apply simp_all
done

lemma lt_diffI:
  assumes major: "i #+ j < k"
      and prem1: "i: nat"
      and prem2: "j: nat"
      and prem3: "k: nat"
    shows "j < k #- i"
apply (insert prem2)
apply (rule major [THEN rev_mp])
apply (rule prem1 [THEN [2] bspec])
apply (rule prem3 [THEN nat_induct])
apply simp
apply (intro ballI impI)
apply (rename_tac v)
apply (erule_tac n="v" in natE)
apply simp_all
done

lemma lt_diffD:
  assumes major: "j < k #- i"
      and prem1: "i: nat"
      and prem2: "j: nat"
      and prem3: "k: nat"
    shows "i #+ j < k"
apply (insert prem2)
apply (rule major [THEN rev_mp])
apply (rule prem1 [THEN [2] bspec])
apply (rule prem3 [THEN nat_induct])
apply simp
apply (intro ballI impI)
apply (rename_tac v)
apply (erule_tac n="v" in natE)
apply simp_all
done

lemma lt_diff_iff:
    "[| i: nat; j: nat; k: nat |] ==> j < k #- i <-> i #+ j < k"
apply (rule iffI)
apply (erule_tac [2] lt_diffI)
apply (erule lt_diffD)
apply assumption+
done

lemma diff_diff_eq_diff_add:
  assumes prem1: "i: nat"
      and prem2: "j: nat"
      and prem3: "k: nat"
    shows "i #- j #- k = i #- (k #+ j)"
apply (rule prem1 [THEN [2] bspec])
apply (rule prem3 [THEN [2] bspec])
apply (rule prem2 [THEN nat_induct])
apply simp
apply (intro ballI)
apply (rename_tac u v)
apply (erule_tac n="v" in natE)
apply simp_all
done

(** Quantifiers Bounded by Natural Number **)
lemmas nat_ltI = nat_into_Ord [THEN [2] ltI]

lemma ball_mem_nat_in_nat:
    "n: nat ==> (ALL x:n. x:nat) <-> True"
apply (blast intro: mem_nat_in_nat)
done

lemma nat_succ_mono:
    "[| n:m; m: nat |] ==> succ(n): succ(m)"
apply (rule ltD)
apply (simp add: nat_ltI)
done

lemma nat_ball_succ:
    "n: nat ==> (ALL x:succ(n). P(x)) <-> P(0) & (ALL x:n. P(succ(x)))"
apply safe
apply (erule bspec)
apply (rule ltD)
apply simp
apply (drule nat_ltI, assumption)
apply (erule bspec)
apply (rule ltD)
apply simp
apply (erule natE)
apply simp+
apply (frule_tac mem_nat_in_nat, assumption)
apply (erule_tac n="x" in natE)
apply simp
apply (rename_tac v)
apply (drule_tac x="v" in bspec)
apply simp_all
apply (rule ltD)
apply (drule_tac i="succ(v)" in ltI)
apply (erule nat_into_Ord)
apply (simp add: succ_lt_iff)
done

lemma nat_bex_succ:
  "n: nat ==> (EX x:succ(n). P(x)) <-> P(0) | (EX x:n. P(succ(x)))"
apply safe
apply simp_all
apply (erule natE)
apply simp
apply (drule_tac x="x" in bspec)
apply simp
apply simp
apply (frule mem_nat_in_nat, assumption)
apply (erule_tac n="x" in natE)
apply simp
apply (rename_tac v)
apply (drule_tac x="v" in bspec)
apply simp
apply (rule ltD)
apply (drule_tac i="succ(v)" in ltI)
apply (erule nat_into_Ord)
apply (simp add: succ_lt_iff)
apply simp
apply (erule natE)
apply simp
apply hypsubst
apply (rule disjI2)
apply (rule bexI, assumption)
apply (rule ltD)
apply (erule nat_0_le)
apply (case_tac "n = succ(x)")
apply simp
apply (rule disjI2)
apply (rule bexI, assumption)
apply (frule_tac i="n" and j="succ(x)" in nat_into_Ord [THEN Ord_linear])
apply (rule nat_into_Ord)
apply (frule mem_nat_in_nat, assumption)
apply (erule nat_succI)
apply simp
apply (blast elim: mem_irrefl mem_asym)
done

lemma nat_ball_cong:
  assumes prem1: "A = A'"
      and prem2: "!!x. x < A' ==> P(x) <-> P'(x)"
      and prem3: "!!x. [| x: A'; A'~: nat |] ==> P(x) <-> P'(x)"
    shows "Ball(A, P) <-> Ball(A', P')"
apply (rule prem1 [THEN ball_cong])
apply (case_tac "A' : nat")
apply (rule prem2)
apply (erule ltI)
apply (erule nat_into_Ord)
apply (erule prem3)
apply assumption
done

lemma nat_bex_cong:
  assumes prem1: "A = A'"
      and prem2: "!!x. x < A' ==> P(x) <-> P'(x)"
      and prem3: "!!x. [| x: A'; A'~: nat |] ==> P(x) <-> P'(x)"
    shows "Bex(A, P) <-> Bex(A', P')"
apply (rule prem1 [THEN bex_cong])
apply (case_tac "A' : nat")
apply (rule prem2)
apply (erule ltI)
apply (erule nat_into_Ord)
apply (erule prem3)
apply assumption
done

lemmas nat_bquant_congs = nat_ball_cong nat_bex_cong

lemma nat_bquant_succ1_1:
  "(ALL x:succ(i).P(x)) <-> P(i) & (ALL x:i. P(x))"
by simp

lemma nat_bquant_succ1_2:
  "(EX  x:succ(i).P(x)) <-> P(i) | (EX x:i. P(x))"
by simp

lemmas nat_bquant_succ1 = nat_bquant_succ1_1 nat_bquant_succ1_2

lemmas nat_bquant_succ2 = nat_ball_succ nat_bex_succ

(*
declare nat_bquant_succ1 [simp del]
declare nat_bquant_succ2 [simp]
*)

lemma complete_induct0:
  "[| i : nat; !! i. [| i : nat; (ALL j: i. P(j)) |] ==> P(i) |] ==> P(i)"
apply (erule complete_induct)
apply simp
done

end
