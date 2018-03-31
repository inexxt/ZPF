module Parity

data Parity : Nat -> Type where
   Even : Parity (n + n)
   Odd  : Parity (S (n + n))

{-
l1: Parity (S (plus j (S j))) -> Parity (S (S (plus j j)))
....
-}

parity : (n:Nat) -> Parity n
parity Z     = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S k)) with (parity k)
    parity (S (S (j + j)))     | Even = ?l1 (Even {n=S j})
    parity (S (S (S (j + j)))) | Odd  ?= (Odd {n=S j})



---------- Proofs ----------
Parity.parity_lemma_1 = proof
  compute
  intros
  rewrite sym (plusSuccRightSucc j j)
  trivial



Parity.l1 = proof
  compute
  intros
  rewrite sym (plusSuccRightSucc j j)
  trivial



{-


parity2 : (n:Nat) -> Parity n
parity2 Z     = Even {n = Z}
parity2 (S k) with (parity2 k)
    parity2 (S (j + j))     | Even ?= Odd {n=j}
    parity2 (S (S (j + j))) | Odd  ?= Even {n=S j}

-}
