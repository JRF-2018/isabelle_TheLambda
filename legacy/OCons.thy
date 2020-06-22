(*
    File:        OCons.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

OCons = OccTools + Cardinal +

consts
  OCons :: [i, i]=>i
  ODestr :: [i, i]=>i
  
defs
  OCons_def  "OCons(n, u) == THE v. EX l T. u = <l, T> & v = <Cons(n, l), T>"
  ODestr_def "ODestr(n, u) == THE v. EX l T. v = <l, T> & u = <Cons(n, l), T>"

end
