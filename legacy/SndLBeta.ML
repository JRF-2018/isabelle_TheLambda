(*
    File:        SndLBeta.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open SndLBeta;


qed_goal "SndLBeta1_LBeta1" SndLBeta.thy
    "<M, N>: SndLBeta1 ==> LBeta1(M, N)"
  (fn [prem] =>
    [(rtac (prem RS SndLBeta1.induct) 1),
     (ALLGOALS (eresolve_tac [LBeta1_baseI, LBeta1_LLamI,
			    LBeta1_LAppI1, LBeta1_LAppI2])),
     (REPEAT (atac 1))]);

qed_goal "LBeta1_SndLBeta1" SndLBeta.thy
    "LBeta1(M, N) ==> <M, N>: SndLBeta1"
  (fn [prem] =>
    [(rtac (prem RS rev_mp) 1),
     (rtac (prem RS LBeta1_type2 RS rev_bspec) 1),
     (LTermOcc.ind_tac "M" [prem RS LBeta1_type1] 1),
     (safe_tac (ZF_cs addSEs LBeta1_LTermEs addSEs LTerm_typeEs)),
     (TRYALL ((dtac (bspec RS mp)) THEN' atac THEN' atac)),
     (ALLGOALS (eresolve_tac SndLBeta1.intrs)),
     (REPEAT (atac 1))]);

qed_goal "SndLBeta1_iff_LBeta1" SndLBeta.thy
    "<M, N> : SndLBeta1 <-> LBeta1(M, N)"
  (fn _ =>
    [(rtac iffI 1),
     (etac LBeta1_SndLBeta1 2),
     (etac SndLBeta1_LBeta1 1)]);

