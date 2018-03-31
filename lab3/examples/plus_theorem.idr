module plus_theorem

{- conversion

plus 3 4
\k => plus k 0
\k => plus 0 k
\k,m => plus (S k) m
\k:Nat => 0+k
\k:Nat => k+0
\k => Z + k
 
-}



plus_nO : (n : Nat) -> n + Z = n
plus_nO Z     = ?pnO_Ocase
plus_nO (S k) = let indH = plus_nO k in ?pnO_Scase





---------- Proofs ----------
{-
plus_theorem.pnO_Scase = proof
  compute
  intros
  rewrite indH
  trivial



plus_theorem.pnO_Ocase = proof
  trivial

-}



