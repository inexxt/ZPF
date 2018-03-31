{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}
data Zero
data Succ n

type One   = Succ Zero
type Two   = Succ One
type Three = Succ Two
type Four  = Succ Three

zero  = undefined :: Zero
one   = undefined :: One
two   = undefined :: Two
three = undefined :: Three
four  = undefined :: Four

class Add a b c | a b -> c where
	add :: a -> b -> c
	add = undefined

instance Add Zero b b
instance Add a b c => Add (Succ a) b (Succ c)

class Mul a b c | a b -> c where
	mul :: a -> b -> c
	mul = undefined

instance Mul Zero b Zero
instance (Mul a b c, Add b c d) => Mul (Succ a) b d

--instance Mul a b c => Mul (Succ a) b c where
--	mul = add 

class Factorial a b | a -> b where
	fac :: a -> b
	fac = undefined

instance Factorial Zero One
instance (Factorial a f, Mul f (Succ a) c) => Factorial (Succ a) c
	