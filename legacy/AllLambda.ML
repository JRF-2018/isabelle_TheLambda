(*
    File:        AllLambda.ML
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

open AllLambda;

qed_goal "LAlpha3_iff_LAlpha2" AllLambda.thy
    "Infinite(LVariable) ==> LAlpha3(M, N) <-> <M, N>: LAlpha2"
  (fn [infv] =>
    [(rtac ([LAlpha3_iff_LAlpha, infv RS 
	     LAlpha2_iff_LAlpha RS iff_sym] 
	  MRS iff_trans) 1)]);

