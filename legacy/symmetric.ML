(*
    File:        symmetric.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)
fun get_const_cterm thy s = 
    let val Some t = Sign.const_type (sign_of thy) s
    in 
	read_cterm (sign_of thy) (s, t) 
    end;

fun make_replset thy ((l, r)::p) = 
    (term_of (get_const_cterm thy l), term_of (get_const_cterm thy r))
    ::(make_replset thy p)
  | make_replset thy [] = [];

fun make_symmetric_replset thy ((l, r)::p) = 
    let val l' = term_of (get_const_cterm thy l);
	val r' = term_of (get_const_cterm thy r)
    in 
	(l', r')::(r', l')::(make_symmetric_replset thy p)
    end
  | make_symmetric_replset thy [] = [];

fun term_tree_replace s (l $ r) = 
         (term_tree_replace s l) $ (term_tree_replace s r)
  | term_tree_replace s (Abs (a, T, u)) = Abs (a, T, term_tree_replace s  u)
  | term_tree_replace s (Const(x, y)) = (case (assoc(s, Const(x, y))) of
					   Some u => u | None => Const(x, y))
  | term_tree_replace s (Var((x, i), t)) = Free(x, t)
  | term_tree_replace s x = x;

structure Symset = struct
  datatype symset = Symset of {replset: (term*term)list,
			       simpset: simpset};

  fun make_symset thy l ss = Symset {replset = make_symmetric_replset thy l,
				    simpset = ss};

  fun addsym thy (Symset {replset, simpset}) l = 
      Symset {replset = replset @ (make_symmetric_replset thy l),
	      simpset = simpset};

  fun op addsimps (Symset {simpset, replset}) l = 
      Symset {replset = replset, 
	      simpset = Simplifier.addsimps (simpset, l)};

  fun make_symmetric_cterm thy (Symset {replset,...}) th =
      cterm_of (sign_of thy) (term_tree_replace replset (#prop (rep_thm th)));

  fun prove_by_symmetry thy (symset as (Symset {simpset=simps, replset})) insts th = 
      let val ct = make_symmetric_cterm thy symset th
      in
	  prove_goalw_cterm [] ct 
	  (fn prems => 
	   [(rtac ((read_instantiate insts th) RSN (2, cut_rl)) 1),
	    (ALLGOALS 
	     (fn i => 
	      (if i > 1 then
		   (REPEAT ((ares_tac [nth(prems, (i - 2))] i)
			    ORELSE
			    (CHANGED (asm_simp_tac simps i))))
	       else
		   (asm_full_simp_tac simps i))))])
      end;

 fun qed_by_symmetry name thy symset insts th =
     bind_thm(name, prove_by_symmetry thy symset insts th);
end;

