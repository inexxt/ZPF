class Fluffy f where
  furry :: (a -> b) -> f a -> f b
 
-- Exercise 1
-- Relative Difficulty: 1
instance Fluffy [] where
  furry = map
 
-- Exercise 2
-- Relative Difficulty: 1
instance Fluffy Maybe where
  furry f (Just x) = Just (f x)
  furry f Nothing = Nothing  
 
-- Exercise 3
-- Relative Difficulty: 5
instance Fluffy ((->) t) where
  furry f g = f . g  
 
newtype EitherLeft t a = EitherLeft (Either a t)
newtype EitherRight t a = EitherRight (Either t a)
 
-- Exercise 4
-- Relative Difficulty: 5
--furry :: (a -> b) -> (EitherLeft t a) -> EitherLeft t b

instance Fluffy (EitherLeft t) where
  furry f (EitherLeft (Left x)) = EitherLeft (Left (f x))
  furry _ (EitherLeft (Right x)) = EitherLeft (Right x)
 
-- Exercise 5
-- Relative Difficulty: 5
instance Fluffy (EitherRight t) where
  furry f (EitherRight (Right x)) = EitherRight (Right (f x))
  furry _ (EitherRight (Left x)) = EitherRight (Left x)


class Misty m where
  banana :: (a -> m b) -> m a -> m b
  unicorn :: a -> m a
  -- Exercise 6
  -- Relative Difficulty: 3
  -- (use banana and/or unicorn)
  furry' :: (a -> b) -> m a -> m b
  furry' f = banana (unicorn . f) 
 
-- Exercise 7
-- Relative Difficulty: 2
instance Misty [] where
  banana f x = concat (map f x)
  unicorn x = [x]

-- Exercise 9
-- Relative Difficulty: 6
instance Misty ((->) t) where
  banana f x = \t -> f (x t) t
  unicorn x = \t -> x
 
-- Exercise 10
-- Relative Difficulty: 6
instance Misty (EitherLeft t) where
  banana f (EitherLeft (Left x))= f x
  banana f (EitherLeft (Right x)) = EitherLeft (Right x)
  unicorn x = EitherLeft (Left x) 
 
-- Exercise 11
-- Relative Difficulty: 6
instance Misty (EitherRight t) where
  banana f (EitherRight (Right x))= f x
  banana f (EitherRight (Left x)) = EitherRight (Left x)
  unicorn x = EitherRight (Right x) 
 
-- Exercise 12
-- Relative Difficulty: 3
jellybean :: (Misty m) => m (m a) -> m a
jellybean = banana id


-- Exercise 13
-- Relative Difficulty: 6
apple :: (Misty m) => m a -> m (a -> b) -> m b
apple ma f = banana (\h -> furry' h ma) f
 

-- Exercise 8
-- Relative Difficulty: 2
instance Misty Maybe where
  banana f (Just x) = f x
  banana _ Nothing = Nothing
  unicorn x = Just x
 

--class Misty m where
-- banana :: (a -> m b) -> m a -> m b
-- unicorn :: a -> m a
-- -- Exercise 6
-- -- Relative Difficulty: 3
-- -- (use banana and/or unicorn)
-- furry' :: (a -> b) -> m a -> m b
-- furry' f = banana (unicorn . f) 


 --Exercise 14
 --Relative Difficulty: 6
moppy :: (Misty m) => [a] -> (a -> m b) -> m [b]
moppy [] f = unicorn []
moppy (a:as) f = apple (moppy as f) (banana (unicorn . (:)) b) where b = f a

 --Exercise 15
 --Relative Difficulty: 6
 --(bonus: use moppy)
sausage :: (Misty m) => [m a] -> m [a]
sausage x = moppy x (jellybean . unicorn)
 
-- Exercise 16
-- Relative Difficulty: 6
-- (bonus: use apple + furry')
banana2 :: (Misty m) => (a -> b -> c) -> m a -> m b -> m c
banana2 f a b = apple b (apple a (unicorn f))
 
-- Exercise 17
-- Relative Difficulty: 6
-- (bonus: use apple + banana2)
banana3 :: (Misty m) => (a -> b -> c -> d) -> m a -> m b -> m c -> m d
banana3 f a b c = apple c $ banana2 f a b  
 
-- Exercise 18
-- Relative Difficulty: 6
-- (bonus: use apple + banana3)
banana4 :: (Misty m) => (a -> b -> c -> d -> e) -> m a -> m b -> m c -> m d -> m e
banana4 f a b c d = apple d $ banana3 f a b c
 
newtype State s a = State {
  state :: (s -> (s, a))
}

-- Exercise 19
-- Relative Difficulty: 9
instance Fluffy (State s) where
  furry f (State g) = State (\s -> let
    (s_new, a) = g s in 
    (s_new, f a))

-- Exercise 20
-- Relative Difficulty: 10
instance Misty (State s) where
  banana f (State g) = State (\s_old -> 
    let (s_new, a) = g s_old in
      (state (f a)) s_new)

  unicorn x = State (\s -> (s, x))
