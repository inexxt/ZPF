{-

:doc Eq

interface Eq ty where
  (==) : ty -> ty -> Bool
  (/=) : ty -> ty -> Bool
-}  
  

occurrences : Eq ty => (item : ty) -> (values : List ty) -> Nat
occurrences item [] = 0
occurrences item (value :: values) = case value == item of
                                          False => occurrences item values
                                          True => 1 + occurrences item values

data Matter = Solid | Liquid | Gas


Eq Matter where
    (==) Solid Solid = True
    (==) Liquid Liquid = True
    (==) Gas Gas = True
    (==) _ _ = False



-- occurrences Liquid [Solid, Liquid, Liquid, Gas]

[myEq] Eq Matter where
    (==) _ _ = True 

-- occurrences @{myEq} Liquid [Solid, Liquid, Liquid, Gas]

