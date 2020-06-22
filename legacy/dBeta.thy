(*
    File:        dBeta.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

dBeta = dLambda + 

consts
  
  dBeta1Rel :: i
  
  dBeta1 :: [i, i]=>o

inductive
  domains "dBeta1Rel" <= "dTerm * dTerm"
  
  intrs
    baseI "[| M: dTerm; N: dTerm |] ==>   \
\                <dApp(dLam(M), N), dSubst(M, 0, N)>: dBeta1Rel"
  
    dLamI "<M, M'>: dBeta1Rel ==> <dLam(M), dLam(M')>: dBeta1Rel"
  
    dAppI1 "[| <M, M'>: dBeta1Rel; N: dTerm |] ==>   \
\                  <dApp(M, N), dApp(M', N)>: dBeta1Rel"
    
    dAppI2 "[| M: dTerm; <N, N'>: dBeta1Rel |] ==>   \
\              <dApp(M, N), dApp(M, N')>: dBeta1Rel"

  type_intrs "dTerm.intrs @ [SigmaI, nat_0I, dSubst_type]"
  type_elims "[SigmaE2]"
  
    
defs

  dBeta1_def
    "dBeta1(M, N) == <M, N>: dBeta1Rel"

end
