{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}
import Control.Monad


class Iso a b where
	iso :: a -> b
	osi :: b -> a

instance Iso a a where
	iso = id
	osi = id

instance Iso ((a, b) -> c) (a -> b -> c) where
	iso = curry
 	osi = uncurry

instance (Iso a b) => Iso [a] [b] where
	iso = map iso
	osi = map osi

instance (Functor f, Iso a b) => Iso (f a) (f b) where
	iso = fmap iso
	osi = fmap osi

instance Iso (a -> b -> c) (b -> a -> c) where
	iso f = \a b -> f b a
	osi = iso

instance (Monad m, Iso a b) => Iso (m a) (m b) where
	iso = ap (return iso)
	osi = ap (return osi)
