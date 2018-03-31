double : Num a => a -> a
double x = x * x

twice : (a -> a) -> a -> a
twice f x = f (f x)

quadruple : Num a => a -> a
quadruple = twice double

