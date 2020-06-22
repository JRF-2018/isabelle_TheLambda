(*
    File:        SndLBeta.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

SndLBeta = LBeta + 

consts
  
  SndLBeta1 :: i
  
inductive
  domains "SndLBeta1" <= "LTerm * LTerm"
  
  intrs
    baseI "LFreeForIn(B, x, A) ==>   \ 
\          <LApp(LLam(x, A), B), Lsubst(A, x, B)>: SndLBeta1"

    LLamI "[| <M, M'>: SndLBeta1;  x: LVariable |] ==>   \ 
\          <LLam(x, M), LLam(x, M')>: SndLBeta1"
  
    LAppI1 "[| <A, A'>: SndLBeta1;  B: LTerm |] ==>   \ 
\           <LApp(A, B), LApp(A', B)>: SndLBeta1"
    
    LAppI2 "[| <B, B'>: SndLBeta1;  A: LTerm |] ==>   \ 
\           <LApp(A, B), LApp(A, B')>: SndLBeta1"

  type_intrs "LTerm.intrs @ [SigmaI, nat_0I, Lsubst_type]"
  type_elims "[SigmaE2,LFreeForInE]"
  
    
end
