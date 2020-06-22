(*
    File:        Nth.thy
    Time-stamp:  <2020-06-22T03:46:28Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: Logics_ZF (of Isabelle2020)
*)

theory Nth imports ZF_aux ZF.List begin

definition mapnth :: "[[i, i]=>i, i]=>i" where
  "mapnth(f, l) == rec(length(l), [],   
                       %n r. r @ [f(n, nth(n, l))])"

lemma UN_succ:
    "(UN z: succ(n). f(z)) = (UN z: n. f(z)) Un f(n)"
apply (rule Un_commute [THEN [2] trans])
apply simp
done

lemmas nth_over_length_lemma = nth_eq_0
lemmas nth_type2 = nth_type

lemma nth_type1:
    "[| n: nat; l: list(A) |] ==> nth(n, l): A Un {0}"
apply (rule_tac i="n" and j="length(l)" in Ord_linear_lt)
apply (erule nat_into_Ord)
apply (rule nat_into_Ord)
apply (rule length_type, assumption)
apply (frule nth_type, assumption)
apply (erule UnI1)
apply (frule nth_eq_0, assumption)
apply (rule le_eqI)
apply (erule sym)
apply (erule nat_into_Ord)
apply blast
apply (frule nth_eq_0, assumption)
apply (erule leI)
apply blast
done

lemma nthlemma_0:
  "(UN y: A. 0) = 0"
	"Collect(0, P) = 0" 
  "{x: A . False} = 0"
	"{x: A . True} = A"
by blast+

lemmas nthlemma = nat_ltI ball_mem_nat_in_nat
  (* nth_Cons nth_0 nth_empty *) UN_succ (* UN_0 UN_constant *)
  Un_assoc[THEN sym] (* lt_nat_in_nat mem_nat_in_nat *)
  nthlemma_0
(* declare nat_ltI [TC] *)

declare lt_nat_in_nat [TC]
declare mem_nat_in_nat [TC]

declare nthlemma [simp]
declare nat_bquant_succ1 [simp del]
declare nat_bquant_succ2 [simp]

lemma nth_app_right:
    assumes major: "l: list(A)"
    and prem: "x < length(l)"
    shows "nth(x, l@m) = nth(x, l)"
apply (rule prem [THEN ltD, THEN rev_bspec])
apply (rule major [THEN list.induct])
apply simp_all
done

lemma nth_app_left:
    "l: list(A) ==> nth(length(l), l @ Cons(x, m)) = x"
apply (erule list.induct)
apply simp_all
done

lemma nth_app_left2 [rule_format]:
  "l: list(A) ==> ALL n: nat. length(l) \<le> n -->
              nth(n, l@m) = nth(n #- length(l), m)"
apply (erule list.induct)
apply simp_all
apply (intro ballI impI)
apply (erule natE)
apply simp_all
done

lemma nth_convert_list_type:
  assumes major: "l: list(B)"
  and prem: "ALL z: length(l). nth(z, l): A"
  shows "l: list(A)"
apply (rule prem [THEN rev_mp])
apply (rule major [THEN list.induct])
apply simp_all
done

lemma nth_map:
  assumes major: "l: list(A)"
  and prem: "n < length(l)"
  shows "nth(n, map(f, l)) = f(nth(n, l))"
apply (rule prem [THEN ltD, THEN rev_bspec])
apply (rule major [THEN list.induct])
apply simp_all
done

lemma nth_inj:
  assumes major: "ALL z: length(l). nth(z, m) = nth(z, l)"
      and prem: "length(m) = length(l)"
      and l_list: "l: list(A)"
      and m_list: "m: list(B)"
    shows "m = l"
apply (rule prem [THEN rev_mp])
apply (rule major [THEN rev_mp])
apply (rule m_list [THEN rev_bspec])
apply (rule l_list [THEN list.induct])
apply simp_all
apply clarify
apply (erule_tac a="x" in list.cases)
apply simp_all
apply blast
done

declare nat_bquant_succ1 [simp]
declare nat_bquant_succ2 [simp del]

lemma nth_existence_lemma:
  assumes major: "ALL z:n. f(z): A"
  and sub: "n: nat"
  shows "EX l: list(A). length(l) = n & (ALL z: n. nth(z, l) = f(z))"
apply (rule major [THEN rev_mp])
apply (rule sub [THEN nat_induct])
apply simp_all
apply clarify
apply (rule_tac x="l@[f(length(l))]" in bexI)
apply (simp_all add: nth_append)
apply blast
done

(** mapnth **)
lemma mapnth_Nil:
    "mapnth(f, []) = []"
apply (unfold mapnth_def)
apply simp
done

lemma mapnth_lemma:
    "n: nat ==> 
       Cons(f(0, a), rec(n, [], %x r. r @ [f(succ(x), nth(x, l))])) = 
          rec(n, [], %x r. r @ [f(x, nth(x, Cons(a, l)))])@ 
                      [f(n, nth(n, Cons(a, l)))]"
apply (erule nat_induct)
apply simp
apply (simp del: app_Cons add: app_Cons [THEN sym])
done

lemma mapnth_Cons:
    "l: list(A) ==>
      mapnth(f, Cons(a, l)) = Cons(f(0, a), mapnth(%x. f(succ(x)), l))"
apply (unfold mapnth_def)
apply (rule mapnth_lemma [THEN sym, THEN [2] trans])
apply simp_all
done

lemma mapnth_Cons2:
  "[| length(l): nat |] ==> 
    mapnth(f, Cons(a, l)) = Cons(f(0, a), mapnth(%x. f(succ(x)), l))"
apply (unfold mapnth_def)
apply (rule mapnth_lemma [THEN sym, THEN [2] trans])
apply simp_all
done

lemma rec_nth_app_right [rule_format]:
    "[| n: nat; l: list(A) |] ==> n \<le> length(l) --> 
        rec(n, [], %n r. r @ [f(n, nth(n, l@m))]) = 
        rec(n, [], %n r. r @ [f(n, nth(n, l))])"
apply (erule nat_induct)
apply (simp_all add: nth_app_right leI)
done

lemma mapnth_type:
  assumes prem1: "l: list(A)"
  and prem2: "!! n x. [| n: nat; x: A |] ==> f(n, x): B"
  shows "mapnth(f, l): list(B)"
apply (unfold mapnth_def)
apply (rule prem1 [THEN list_append_induct])
apply simp
apply (simp add: rec_nth_app_right)
apply (erule app_type)
apply (rule list.intros)
apply (rule prem2)
apply simp_all
done

lemma mapnth_app_last:
  "l: list(A) ==>
      mapnth(f, l@[a]) = mapnth(f, l) @ [f(length(l), a)]"
apply (unfold mapnth_def)
apply (drule_tac B="list(cons(a, A))" in rev_subsetD)
apply (rule list_mono)
apply blast
apply (simp add: rec_nth_app_right)
apply (simp add: nth_app_left2)
done

lemma mapnth_type2:
  "l: list(A) ==> mapnth(f, l): list({f(n, x). <n,x>: nat*A})"
apply (rule mapnth_type, assumption)
apply (rule_tac P="%y. y:{f(n, x). <n,x>: nat*A}" 
         and b="f(n,x)" and a="split(f, <n, x>)" in ssubst)
apply simp_all
apply blast
done

lemma length_mapnth:
    "l: list(A) ==> length(mapnth(f, l)) = length(l)"
apply (erule list_append_induct)
apply (frule_tac [2] f="f" in mapnth_type2)
apply (simp_all add: mapnth_Nil mapnth_app_last)
apply (subst length_app, assumption)
apply (rule list.intros)
apply (rule_tac b="f(length(y), x)" in ssubst)
apply (rule_tac [2] RepFunI)
apply (rule_tac [2] a="length(y)" and b="x" in SigmaI)
apply simp_all
done

lemma nth_mapnth:
  assumes major: "l: list(A)"
  and prem: "n < length(l)"
  shows "nth(n, mapnth(f, l)) = f(n, nth(n, l))"
apply (rule prem [THEN ltD, THEN rev_bspec])
apply (rule major [THEN list_append_induct])
apply (simp_all add: mapnth_app_last)
apply (frule_tac f="f" in mapnth_type2)
apply (frule_tac f="f" in length_mapnth)
apply safe
apply (simp_all add: nth_app_left nth_app_right nth_app_left2)
done

lemma map_mapnth:
  "l: list(A) ==> map(f, mapnth(g, l)) = mapnth(%x r. f(g(x, r)), l)"
apply (frule_tac f="g" in mapnth_type2)
apply (rule nth_inj)
prefer 4 apply (rule map_type2, assumption)
prefer 3 apply (rule mapnth_type2, assumption)
apply (simp_all add: length_mapnth nth_map nth_mapnth)
done

lemma mapnth_map:
  "l: list(A) ==> mapnth(f, map(g, l)) = mapnth(%x r. f(x, g(r)), l)"
apply (frule_tac h="g" in map_type2)
apply (rule nth_inj)
prefer 4 apply (erule mapnth_type2)
prefer 3 apply (erule mapnth_type2)
apply (simp_all add: length_mapnth nth_map nth_mapnth)
done

lemma mapnth_mapnth:
  "l: list(A) ==> mapnth(f, mapnth(g, l)) = mapnth(%x r. f(x, g(x, r)), l)"
apply (frule_tac f="g" in mapnth_type2)
apply (rule nth_inj)
prefer 4 apply (erule mapnth_type2)
prefer 3 apply (erule mapnth_type2)
apply (simp_all add: length_mapnth nth_mapnth)
done

(** nth_0E **)
lemma nth_0E_lemma:
    "l: list(A) ==> ALL a. 0 < length(l) --> nth(0, l) = a
       --> (EX m: list(A). a: A & l = Cons(a, m))"
apply (erule list.cases)
apply simp_all
done

lemma nth_0E:
  assumes major: "nth(0, l) = a"
  and l_list: "l: list(A)"
  and l_len: "0 < length(l)"
  and prem: "!!m. [| a: A; m: list(A); l = Cons(a, m) |] ==> P"
  shows "P"
apply (rule l_list [THEN nth_0E_lemma, 
                     THEN spec, THEN mp, THEN mp, THEN bexE]) 
apply (erule_tac [3] conjE)
apply (rule_tac [3] prem)
apply ((rule major l_len) | assumption)+
done

lemma length_0E:
  assumes major: "length(l) = 0"
  and l_list: "l: list(A)"
  and prem: "l = [] ==> P"
  shows "P"
apply (rule l_list [THEN list.cases])
apply (erule prem)
apply (insert major)
apply simp
done

declare mapnth_type2 [TC]
declare mapnth_type [TC]

lemmas nth_ss_lemmas = mapnth_Nil mapnth_Cons2
   add_0_right (* add_succ_right length_app app_right_Nil *)
   nth_app_right nth_app_left Cons_iff

declare nth_ss_lemmas [simp]

end
