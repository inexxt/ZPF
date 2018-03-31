import Data.Vect


{-

data Elem : a -> Vect k a -> Type where
   Here : Elem x (x :: xs)
   There : (later : Elem x xs) -> Elem x (y :: xs)

-}

total
removeElem : (value : a) -> (xs : Vect (S n) a) -> (prf : Elem value xs) ->
             Vect n a
removeElem value (value :: ys) Here = ys
{- removeElem value (y :: []) (There later) = absurd later-}
removeElem {n = (S k)} value (y :: ys) (There later)
     = y :: removeElem value ys later



not_in_nil : Elem value [] -> Void
not_in_nil Here impossible
not_in_nil (There _) impossible
