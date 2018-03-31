import Data.Vect

{-
data Vect : Nat -> Type -> Type where
   Nil  : Vect Z a
   (::) : a -> Vect k a -> Vect (S k) a
-}
	

my_vect_map : (a -> b) -> Vect n a -> Vect n b
my_vect_map f Nil = Nil
my_vect_map f (a::as) = ((f a)::(my_vect_map f as))


insert : Ord elem => (x : elem) -> (xsSorted : Vect k elem) -> Vect (S k) elem
insert x Nil = x :: Nil
insert x (a::as) = if x < a then (x :: (a :: as)) else (a :: (insert x as))

insSort : Ord elem => Vect n elem -> Vect n elem
insSort Nil = Nil
insSort (a::as) = insert a (insSort as)


