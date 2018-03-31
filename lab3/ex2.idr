import Data.Vect

create_empties : Vect n (Vect 0 elem)
create_empties = replicate  _ []

{-
flatten : Vect m (Vect n elem) -> Vect (mult n m) elem
flatten Nil = Nil
flatten (x::xs) = x ++ flatten xs
-}


transpose_mat : Vect m (Vect n elem) -> Vect n (Vect m elem)
transpose_mat Nil = create_empties
transpose_mat (r::rs) = zipWith (::) r (transpose_mat rs) 

addMatrix : Num a => Vect n (Vect m a) -> Vect n (Vect m a) -> Vect n (Vect m a)
addMatrix Nil Nil = Nil
addMatrix (a::as) (b::bs) = (zipWith (+) a b)::(addMatrix as bs)

mulMatVect : Num a => Vect n a -> Vect n (Vect m a) -> Vect m a
mulMatVect n m = [sum (zipWith (*) x n) | x <- transpose m]


multMatrix : Num a => Vect m (Vect n a) -> Vect n (Vect p a) -> Vect m (Vect p a)
multMatrix Nil v = Nil
multMatrix (n::ns) m = (mulMatVect n m) :: (multMatrix ns m)
multMatrix m Nil = transpose (multMatrix (transpose Nil) (transpose m))

