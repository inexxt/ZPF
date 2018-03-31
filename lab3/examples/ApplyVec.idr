import Data.Vect

{-
vApp : Vect n (a -> b) -> Vect n a -> Vect n b
vApp []       []         = []
vApp (f :: fs) (a :: as) = f a :: vApp fs as
-}


total
vApp : {a:Type} -> {b:Type} -> {n:Nat} ->  Vect n (a -> b) -> Vect n a -> Vect n b
vApp  []       []         = []
vApp (f :: fs) (a :: as) = f a :: vApp fs as

