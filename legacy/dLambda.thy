(*
    File:        dLambda.thy
    Author:      JRF
    Web:         http://jrf.cocolog-nifty.com/software/2016/01/post.html
    Logic Image: ZF
    Remark:      This is a legacy code before 1999.
*)

dLambda = dTermDef + OCons + FinCard + Arith + 

consts
  dAbst  :: [i, i, i]=>i
  dLift  :: [i, i]=>i
  dSubst :: [i, i, i]=>i

  dDeg   :: i=>i
  dFV :: i=>i
  dProp  :: i

  dLamDegBase :: [i, i]=>i
  dLamDeg :: [i, i]=>i
  dBoundBy :: [i, i, i]=>o
  
defs
  
  dAbst_def
    "dAbst(M, x, n) == dTerm_rec(M,   \
\          %y. lam i: nat. if(x=y, dBound(i), dVar(y)),   \
\          %j. lam i: nat. dBound(j),   \
\          %N r. lam i: nat. dLam(r`succ(i)),   \
\          %A B ra rb. lam i: nat. dApp(ra`i, rb`i)) ` n"
  
  dLift_def
    "dLift(M, n) == dTerm_rec(M,   \
\          %x. lam i: nat. dVar(x),   \
\          %j. lam i: nat. if (j < i, dBound(j), dBound(succ(j))), \
\          %N r. lam i: nat. dLam(r`succ(i)),   \
\          %A B ra rb. lam i: nat. dApp(ra`i, rb`i)) ` n"

  dSubst_def
    "dSubst(M, n, N) == dTerm_rec(M,   \
\          %x. lam i: nat. lam m: dTerm. dVar(x),   \
\          %j. lam i: nat. lam m: dTerm. if (i < j, dBound(j #- 1),   \
\                                         if (i=j, m, dBound(j))),   \
\          %N r. lam i: nat. lam m: dTerm. dLam(r`succ(i)`dLift(m, 0)),   \
\          %A B ra rb. lam i: nat. lam m: dTerm. dApp(ra`i`m, rb`i`m))`n`N"


  dDeg_def 
    "dDeg(M) == dTerm_rec(M, %x. 0, %n. succ(n), %N r. r #- 1,   \
\                            %A B rm rn. rm Un rn)"

  dFV_def
    "dFV(M) == {x: LVariable. EX l.  <l, TdVar(x)>: dOcc(M)}"

  dProp_def "dProp == {M: dTerm. dDeg(M) = 0}"

  dLamDegBase_def
   "dLamDegBase(l, M) == {v: dOcc(M). EX m. v = <m, TdLam> & m ~= l &   \
\                                     initseg(nat, m, l)}"

  dLamDeg_def
   "dLamDeg(l, M) == |dLamDegBase(l, M)|"

  dBoundBy_def
    "dBoundBy(u, v, M) == M: dTerm & u: dOcc(M) & v: dOcc(M) &  \
\      (EX n l m x. u = <m, TdBound(n)> & v = <l, TdLam> &   \
\        m = l @ x & dLamDeg(x, dsubterm(M, l)) = succ(n))"

end
