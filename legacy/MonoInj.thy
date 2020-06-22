(*
    File:        MonoInj.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

MonoInj  =  Fixedpt + Finite +

consts
  mono_inj_pair :: [i,i=>i,i=>i]=>o

defs
  mono_inj_pair_def
    "mono_inj_pair(D,F,G) == (ALL x. x <= D --> G(F(x)) = x) &   \
\        (ALL x y. x <= y & y <= D --> F(x) <= F(y)) &   \
\        (ALL x y. x <= y & y <= F(D) --> G(x) <= G(y))"

end
