(*
    File:        Infinite.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

Infinite = Finite +

consts
  Infinite :: i => o
  
defs
  Infinite_def "Infinite(X) == ALL F: Fin(X). X ~= F"

end
