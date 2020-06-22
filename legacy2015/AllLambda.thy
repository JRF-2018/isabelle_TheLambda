(*
    File:        AllLambda.thy
    Time-stamp:  <2016-01-06T17:58:00Z>
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF (of Isabelle2015)
*)

theory AllLambda
imports dB dBeta SndLAlpha SndLBeta Length FNumber FinBndEx
begin

lemma LAlpha3_iff_LAlpha2:
  assumes infv: "Infinite(LVariable)"
  shows "LAlpha3(M, N) <-> <M, N>: LAlpha2"
apply (rule iff_trans [OF LAlpha3_iff_LAlpha
        infv [THEN LAlpha2_iff_LAlpha, THEN iff_sym]])
done

end
