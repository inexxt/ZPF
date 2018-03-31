import Data.Vect
import Control.Monad

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex n Nil = Nothing
tryIndex 0 (v::vs) = Just v
tryIndex n (v::vs) = if n < 0 then Nothing else tryIndex (n-1) vs

-- odpowiednik take dla list
take : (n: Nat) -> Vect (n+m) a -> Vect n a

take Z Nil = Nil
take (S n) (v::vs) = v::(Main.take n vs)

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries pos va vb = case (tryIndex pos va, tryIndex pos vb) of
	(Nothing, Nothing) => Nothing
	(Just x, Just y) => Just (x + y)


-- sumEntries pos va vb = liftM2 (+) (tryIndex pos va) (tryIndex pos vb)