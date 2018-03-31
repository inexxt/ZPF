module Spr where
import Data.Array
import Data.Monoid

class MFoldable t where
    mfoldr :: (a -> b -> b) -> b -> t a -> b
	-- | Map each element of the structure to a monoid,
	-- and combine the results.
    mfoldMap :: (Monoid m) => (a -> m) -> t a -> m
    mfoldMap f as = mfoldr (\a b -> mappend (f a) b) mempty as
    
    mfoldl :: (a -> b -> a) -> a -> t b -> a
    mfoldl f = mfoldr (flip f)

instance MFoldable [] where
    mfoldr f b [] = b
    mfoldr f b (a:as) = f a (mfoldr f b as) 
    
    
instance MFoldable Maybe where
    mfoldr f b Nothing = b
    mfoldr f b (Just a) = f a b

instance Ix i => MFoldable (Array i) where
    mfoldr f b arr = mfoldr f b (elems arr)



-- | The concatenation of all the elements of a container of lists.
concat :: MFoldable t => t [a] -> [a]
concat = mfoldr (++) []

map :: MFoldable t => (a -> b) -> t a -> [b]
map f as = mfoldr (\a b -> (f a):b) [] as

-- | Map a function over all the elements of a container and concatenate
-- the resulting lists.
concatMap :: MFoldable t => (a -> [b]) -> t a -> [b]
concatMap f = mfoldr (\a b -> (f a) ++ b) []

-- | 'and' returns the conjunction of a container of Bools.  For the
-- result to be 'True', the container must be finite; 'False', however,
-- results from a 'False' value finitely far from the left end.
and :: MFoldable t => t Bool -> Bool
and ts = mfoldr (&&) True ts 
-- | 'or' returns the disjunction of a container of Bools.  For the
-- result to be 'False', the container must be finite; 'True', however,
-- results from a 'True' value finitely far from the left end.
or :: MFoldable t => t Bool -> Bool
or ts = mfoldr (||) False ts
-- | Determines whether any element of the structure satisfies the predicate.
any :: MFoldable t => (a -> Bool) -> t a -> Bool
any f ts = Spr.or (Spr.map f ts)

-- | Determines whether all elements of the structure satisfy the predicate.
all :: MFoldable t => (a -> Bool) -> t a -> Bool
all f ts = Spr.and (Spr.map f ts)

-- | The 'sum' function computes the sum of the numbers of a structure.
sum :: (MFoldable t, Num a) => t a -> a
sum ts = mfoldr (+) 0 ts

-- | The largest element of a non-empty structure.
-- maximum :: (MFoldable t, Ord a) => t a -> Maybe a
-- maximum ts = mfoldr (\a b -> if a > b then a else b) head (Spr.map id ts) ts
-- -- | Does the element occur in the structure?
elem :: (MFoldable t, Eq a) => a -> t a -> Bool
elem a as = Spr.any (\x -> x == a) as

-- -- | The 'find' function takes a predicate and a structure and returns
-- -- the leftmost element of the structure matching the predicate, or
-- -- 'Nothing' if there is no such element.
find :: MFoldable t => (a -> Bool) -> t a -> Maybe a
find f as = mfoldr (\a b -> if f a then Just a else b) Nothing as